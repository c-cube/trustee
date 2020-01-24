
module Expr = Kernel_of_trust.Expr
module Thm = Kernel_of_trust.Thm
module Fmt = CCFormat

module Int_tbl = CCHashtbl.Make(CCInt)

type 'a gen = unit -> 'a option

(** Namespaced identifier *)
type name = string list * string
type term = Expr.t
type type_op = Expr.t
type type_ = Expr.t
type const = Expr.t
type var = Expr.var
type thm = Thm.t

type obj =
  | Int of int
  | Name of name
  | List of obj list
  | Type_operator of type_op
  | Type of type_
  | Var of var
  | Term of term
  | Thm of thm

module Name = struct
  type t = name
  let pp out (path,n) =
    match path with
    | [] -> Fmt.fprintf out "%S" n
    | _ -> Fmt.fprintf out "\"%s.%s\"" (String.concat "." path) n
end

module Obj_ = struct
  type t = obj

  let rec pp out = function
    | Int i -> Fmt.fprintf out "[int %d]" i
    | Name n -> Fmt.fprintf out "[name %a]" Name.pp n
    | List l -> Fmt.fprintf out "[@[List %a@]]" (Fmt.Dump.list pp) l
    | Type_operator s -> Fmt.fprintf out "[@[type-op@ %a@]" Expr.pp s
    | Type s -> Fmt.fprintf out "[@[type@ %a@]" Expr.pp s
    | Var s -> Fmt.fprintf out "[@[var@ %a@]]" Expr.Var.pp s
    | Term s -> Fmt.fprintf out "[@[term@ %a@]]" Expr.pp s
    | Thm s -> Fmt.fprintf out "[@[thm@ %a@]]" Thm.pp s
end

type article = {
  assumptions: thm list;
  theorems: thm list;
}

type vm = {
  mutable vm_stack: obj list;
  vm_dict: obj Int_tbl.t;
  mutable vm_assumptions: thm list;
  mutable vm_theorems: thm list;
}

let create () : vm = {
  vm_stack=[];
  vm_dict=Int_tbl.create 32;
  vm_assumptions=[];
  vm_theorems=[];
}

module Gen_ = struct
  type 'a t = 'a gen

  let map f g () = match g() with
    | Some x -> Some (f x)
    | None -> None

  let rec filter f g () = match g() with
    | Some x as r when f x -> r
    | Some _ -> filter f g ()
    | None -> None

  let rec iter f g = match g() with
    | None -> ()
    | Some x -> f x; iter f g
end

module VM = struct
  type t = vm

  let pp out (self:t) =
    let pp_pair out (i,obj) =
      Fmt.fprintf out "(@[%d :=@ %a@])" i Obj_.pp obj
    in
    Fmt.fprintf out
      "{@[<hv>vm.stack=%a;@ dict=[@[%a@]];@ assumptions=%a;@ theorems=%a@]}"
      (Fmt.Dump.list Obj_.pp) self.vm_stack
      (Fmt.Dump.list pp_pair) (Int_tbl.to_list self.vm_dict)
      (Fmt.Dump.list Thm.pp) self.vm_assumptions
      (Fmt.Dump.list Thm.pp) self.vm_theorems

  let push_obj self o =
    Fmt.printf "OT.vm.push %a@." Obj_.pp o;
    self.vm_stack <- o :: self.vm_stack

  let pop1 self =
    match self.vm_stack with
    | o :: st -> self.vm_stack <- st; o
    | [] -> Error.errorf "OT.vm.pop1: empty stack@ in %a" pp self

  let pop2 self =
    match self.vm_stack with
    | o1 :: o2 :: st -> self.vm_stack <- st; o1, o2
    | [_] | [] -> Error.errorf "OT.vm.pop2: empty stack@ in %a" pp self
end

module Parse_ = struct
  let c_is_num = function '0' .. '9' -> true | _ -> false
  let is_num s = CCString.for_all c_is_num s

  (* cleanup: remove comments and empty lines *)
  let cleanup_g g =
    g
    |> Gen_.map String.trim
    |> Gen_.filter
      (function
        | "" -> false
        | s when String.get s 0 = '#' -> false
        | _ -> true)

  (* quoted string: push name *)
  let process_name vm s =
    let s = String.sub s 1 (String.length s-2) in
    let l = List.rev @@ String.split_on_char '.' s in
    let name: name =
      match l with
      | [] -> Error.errorf "OT: empty string not allowed"
      | [x] -> [], x
      | x :: rest -> List.rev rest, x
    in
    VM.push_obj vm (Name name)

  let process_int vm s =
    let n =
      try int_of_string s
      with _ -> Error.errorf "OT: cannot convert integer %S" s
    in
    VM.push_obj vm (Int n)

  let err_bad_stack_ vm what =
    Error.errorf "@[<2>OT.%s: wrong stack@ in %a@]" what VM.pp vm

  let err_not_impl_ vm what =
    Error.errorf "OT: not implemented: %s@ in %a" what VM.pp vm

  let abs_term vm =
    match vm.vm_stack with
    | Term t :: Var v :: st ->
      vm.vm_stack <- Term (Expr.lambda v t) :: st
    | _ ->
      Error.errorf "@[<2>OT.abs_term: wrong stack@ in %a@]" VM.pp vm

  let app_term vm =
    match VM.pop2 vm with
    | Term x, Term f -> VM.push_obj vm @@ Term (Expr.app f x)
    | _ -> err_bad_stack_ vm "app_term"

  let assume vm =
    match VM.pop1 vm with
    | Term x -> VM.push_obj vm @@ Thm (Thm.assume x)
    | _ -> err_bad_stack_ vm "assume"

  let version vm =
    match VM.pop1 vm with
    | Int 6 -> ()
    | Int n -> Error.errorf "OT: unsupported version %d" n
    | _ -> err_bad_stack_ vm "version"

  let axiom vm =
    match VM.pop2 vm with
    | Term t, List hyps ->
      let hyps = List.map (function Term t -> t | _ -> err_bad_stack_ vm "axiom") hyps in
      let ax = Thm.axiom hyps t in
      Format.printf "@{<Yellow>OT.add-assumption@} %a@." Thm.pp ax;
      vm.vm_assumptions <- ax :: vm.vm_assumptions;
      VM.push_obj vm (Thm ax)
    | _ -> err_bad_stack_ vm "axiom"

  let nil vm = VM.push_obj vm @@ List[]

  (* TODO *)
  let abs_thm vm = err_not_impl_ vm "abs_thm"
  let app_thm vm = err_not_impl_ vm "app_thm"
  let def vm = err_not_impl_ vm "def"

  let process_line (vm:vm) s : unit =
    Format.printf "process line: %S@." s;
    assert (s <> "");
    if s.[0] = '"' then (
      process_name vm s
    ) else if is_num s then (
      process_int vm s
    ) else (
      match s with
      | "absTerm" -> abs_term vm
      | "absThm" -> abs_thm vm
      | "appTerm" -> app_term vm
      | "appThm" -> app_thm vm
      | "assume" -> assume vm
      | "axiom" -> axiom vm
      | "version" -> version vm
      | "nil" -> nil vm
      | _ ->
        Error.errorf "OT: unknown command %s@." s
    )

  let parse_gen_exn (g:string gen) : article =
    let vm = create() in
    Gen_.iter (process_line vm) @@ cleanup_g g;
    { assumptions= vm.vm_assumptions;
      theorems= vm.vm_theorems;
    }
end

let parse_gen_exn = Parse_.parse_gen_exn

let parse_gen g : _ result =
  try Ok (parse_gen_exn g)
  with Error.Error msg -> Error msg

let parse_exn (s:string) : article =
  let g = CCString.Split.gen_cpy ~by:"\n" s in
  parse_gen_exn g

let parse s : _ result =
  try Ok (parse_exn s)
  with Error.Error msg -> Error msg

module Article = struct
  type t = article

  let pp out self =
    Fmt.fprintf out "@{@[<hv>article.assumptions=%a; theorems=%a]@}"
      (Fmt.Dump.list Thm.pp) self.assumptions
      (Fmt.Dump.list Thm.pp) self.theorems
end
