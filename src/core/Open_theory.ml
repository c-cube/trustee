
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
    | [] -> Fmt.string out n
    | _ -> Fmt.fprintf out "%s.%s" (String.concat "." path) n
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

  let push_obj self o =
    Fmt.printf "OT.vm.push %a@." Obj_.pp o;
    self.vm_stack <- o :: self.vm_stack
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

  let process_line (vm:vm) s : unit =
    Format.printf "line: %S@." s;
    assert (s <> "");
    if s.[0] = '"' then (
      (* string *)
      let s = String.sub s 1 (String.length s-2) in
      let l = List.rev @@ String.split_on_char '.' s in
      let name: name =
        match l with
        | [] -> Error.errorf "OT: empty string not allowed"
        | [x] -> [], x
        | x :: rest -> List.rev rest, x
      in
      VM.push_obj vm (Name name)
    ) else if is_num s then (
      let n =
        try int_of_string s
        with _ -> Error.errorf "OT: cannot convert integer %S" s
      in
      VM.push_obj vm (Int n)
    ) else (
      ()
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
