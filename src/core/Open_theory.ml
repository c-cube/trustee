
open Trustee_kot
module Fmt = CCFormat

module Int_tbl = CCHashtbl.Make(CCInt)

type 'a gen = unit -> 'a option

(** Namespaced identifier *)
type name = string list * string
type term = Expr.t
type type_op = Expr.t list -> Expr.t
type type_ = Expr.t
type var = Expr.var
type thm = Thm.t
type const = type_ -> Expr.t

type obj =
  | Int of int
  | Name of name
  | List of obj list
  | Type_operator of name*type_op
  | Type of type_
  | Const of name*const
  | Var of var
  | Term of term
  | Thm of thm

module Name = struct
  type t = name
  let debug out (path,n) =
    match path with
    | [] -> Fmt.fprintf out "%S" n
    | _ -> Fmt.fprintf out "\"%s.%s\"" (String.concat "." path) n
  let to_string (path,n) =
    match path with
    | [] -> n
    | _ -> String.concat "." path ^ "." ^ n
end

module Obj_ = struct
  type t = obj

  let rec pp out = function
    | Int i -> Fmt.fprintf out "[int %d]" i
    | Name n -> Fmt.fprintf out "[name %a]" Name.debug n
    | List l -> Fmt.fprintf out "[@[List %a@]]" (Fmt.Dump.list pp) l
    | Type_operator (n,_s) -> Fmt.fprintf out "[@[type-op@ %a@]]" Name.debug n
    | Type s -> Fmt.fprintf out "[@[type@ %a@]]" Expr.pp s
    | Var s -> Fmt.fprintf out "[@[var@ %a@]]" Expr.Var.pp s
    | Term s -> Fmt.fprintf out "[@[term@ %a@]]" Expr.pp s
    | Const (n,_) -> Fmt.fprintf out "[@[const@ %a@]]" Name.debug n
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
    | [] -> error_ (fun out () -> Fmt.fprintf out "OT.vm.pop1: empty stack@ in %a" pp self)

  let pop2 self =
    match self.vm_stack with
    | o1 :: o2 :: st -> self.vm_stack <- st; o1, o2
    | [_] | [] ->
      error_ (fun out () -> Fmt.fprintf out "OT.vm.pop2: empty stack@ in %a" pp self)

  let pop3 self =
    match self.vm_stack with
    | o1 :: o2 :: o3 :: st -> self.vm_stack <- st; o1, o2, o3
    | [_;_] | [_] | [] ->
      error_ (fun out () -> Fmt.fprintf out "OT.vm.pop3: empty stack@ in %a" pp self)
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
      | [] -> errorf_ (fun k->k"OT: empty string not allowed")
      | [x] -> [], x
      | x :: rest -> List.rev rest, x
    in
    VM.push_obj vm (Name name)

  let process_int vm s =
    let n =
      try int_of_string s
      with _ -> errorf_ (fun k->k"OT: cannot convert integer %S" s)
    in
    VM.push_obj vm (Int n)

  let err_bad_stack_ vm what =
    errorf_ (fun k->k"@[<2>OT.%s: wrong stack@ in %a@]" what VM.pp vm)

  let err_not_impl_ vm what =
    errorf_ (fun k->k"OT: not implemented: %s@ in %a" what VM.pp vm)

  let abs_term vm =
    match vm.vm_stack with
    | Term t :: Var v :: st ->
      vm.vm_stack <- Term (Expr.lambda v t) :: st
    | _ ->
      errorf_ (fun k->k"@[<2>OT.abs_term: wrong stack@ in %a@]" VM.pp vm)

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
    | Int n -> errorf_ (fun k->k"OT: unsupported version %d" n)
    | _ -> err_bad_stack_ vm "version"

  let axiom vm =
    match VM.pop2 vm with
    | Term t, List hyps ->
      let hyps = List.map (function Term t -> t | _ -> err_bad_stack_ vm "axiom") hyps in
      let ax, _ = Thm.axiom "_ot_axiom" hyps t in
      Format.printf "@{<Yellow>OT.add-assumption@} %a@." Thm.pp ax;
      vm.vm_assumptions <- ax :: vm.vm_assumptions;
      VM.push_obj vm (Thm ax)
    | _ -> err_bad_stack_ vm "axiom"

  let type_op vm = match VM.pop1 vm with
    | Name n ->
      begin match n with
        | [], "bool" -> VM.push_obj vm (Type_operator (n,fun [] -> Expr.bool))
        | [], "->" -> VM.push_obj vm (Type_operator (n,fun [a;b] -> Expr.arrow a b))
        | _ -> err_bad_stack_ vm "typeOf"
      end [@warning "-8"]
    | _ -> err_bad_stack_ vm "typeOp"

  let def vm = match VM.pop2 vm with
    | Int k, x ->
      Int_tbl.replace vm.vm_dict k x;
      VM.push_obj vm x; (* push x back *)
    | _ -> err_bad_stack_ vm "def"

  let cons vm = match VM.pop2 vm with
    | List k, x -> VM.push_obj vm (List (x::k))
    | _ -> err_bad_stack_ vm "cons"

  let nil vm = VM.push_obj vm @@ List[]

  let ref vm = match VM.pop1 vm with
    | Int n ->
      begin match Int_tbl.find vm.vm_dict n with
        | exception Not_found ->
          errorf_ (fun k->k"didn't find object %d in dictionary" n)
        | x -> VM.push_obj vm x
      end
    | _ -> err_bad_stack_ vm "ref"

  let remove vm = match VM.pop1 vm with
    | Int n ->
      begin match Int_tbl.find vm.vm_dict n with
        | exception Not_found ->
          errorf_ (fun k->k"didn't find object %d in dictionary" n)
        | x ->
          Int_tbl.remove vm.vm_dict n;
          VM.push_obj vm x
      end
    | _ -> err_bad_stack_ vm "remove"

  let var_type vm = match VM.pop1 vm with
    | Name ([], n) -> VM.push_obj vm (Type (Expr.new_var' n Expr.type_))
    | Name _ -> err_bad_stack_ vm "varType: bad name for a type var"
    | _ -> err_bad_stack_ vm "var_type"

  let op_type vm = match VM.pop2 vm with
    | List l, Type_operator (_,f) ->
      let l = List.map (function Type t -> t | _ -> errorf_ (fun k->k"expected types")) l in
      VM.push_obj vm (Type (f l))
    | _ -> err_bad_stack_ vm "opType"

  let const vm = match VM.pop1 vm with
    | Name n  ->
      begin match n with
        | [], "=" ->
          let c ty =
            match Core.unfold_arrow ty with
            | [a;_], _ -> Expr.app Expr.eq_const a
            | _ -> errorf_ (fun k->k"cannot make `=` with type %a" Expr.pp ty)
          in
          VM.push_obj vm (Const (n, c))
        | [], "select" ->
          let c ty =
            match Core.unfold_arrow ty with
            | [_], a -> Expr.app Expr.select_const a
            | _ -> errorf_ (fun k->k"cannot make `select` with type %a" Expr.pp ty)
          in
          VM.push_obj vm (Const (n, c))
        | _ -> errorf_ (fun k->k"no constant named %a" Name.debug n)
      end [@warning "-8"]
    | _ -> err_bad_stack_ vm "const"

  let var vm = match VM.pop2 vm with
    | Type ty, Name ([], n) ->
      VM.push_obj vm (Var (Expr.new_var n ty))
    | _, Name n ->
      errorf_ (fun k->k"bad name for a var: %a" Name.debug n)
    | _ -> err_bad_stack_ vm "var"

  let const_term vm = match VM.pop2 vm with
    | Type ty, Const (_,c)  ->
      VM.push_obj vm (Term (c ty))
    | _ -> err_bad_stack_ vm "constTerm"

  let var_term vm = match VM.pop1 vm with
    | Var v -> VM.push_obj vm (Term (Expr.var v))
    | _ -> err_bad_stack_ vm "varTerm"

  let define_const vm = match VM.pop2 vm with
    | Term t, Name n ->
      (* make a definition [n := t] *)
      let thm, c, vars = Core.new_poly_def (Name.to_string n) t in
      Format.printf "@[<2>@{<Yellow>## define const@} %a@ with thm %a@ :vars %a@]@."
        Name.debug n Thm.pp thm (Fmt.Dump.list Expr.Var.pp) vars;
      (* type of [c] applied to [vars] *)
      let c_ty_vars =
        Expr.ty_exn @@ Expr.app_l c (List.map Expr.var vars)
      in
      let mk_c ty =
        let subst =
          try Core.unify_exn c_ty_vars ty
          with Core.Unif_fail (t1,t2,subst) ->
            errorf_ (fun k->k"unification failed@ between `%a`@ and `%a`@ with subst %a"
                        Expr.pp t1 Expr.pp t2 Expr.Subst.pp subst)
        in
        Expr.app_l c
          (List.map
             (fun v -> Expr.Subst.find subst v |> CCOpt.get_or ~default:(Expr.var v))
             vars)
      in
      VM.push_obj vm (Const (n, mk_c));
      VM.push_obj vm (Thm thm);
    | _ -> err_bad_stack_ vm "defineConst"

  let thm vm = match VM.pop3 vm with
    | Term _phi, List l, Thm thm ->
      let _l = List.map (function Term t->t | _ -> err_bad_stack_ vm "thm") l in
      (* FIXME: alpha rename with [l] and [phi] *)
      Format.printf "@[<1>@{<Green>## add theorem@}@ %a@]@." Thm.pp thm;
      vm.vm_theorems <- thm :: vm.vm_theorems
    | _ -> err_bad_stack_ vm "thm"

  let pop vm = match VM.pop1 vm with
    | _ -> ()

  (* TODO *)
  let abs_thm vm = err_not_impl_ vm "abs_thm"
  let app_thm vm = err_not_impl_ vm "app_thm"

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
      | "typeOp" -> type_op vm
      | "def" -> def vm
      | "cons" -> cons vm
      | "ref" -> ref vm
      | "varType" -> var_type vm
      | "opType" -> op_type vm
      | "const" -> const vm
      | "constTerm" -> const_term vm
      | "var" -> var vm
      | "varTerm" -> var_term vm
      | "defineConst" -> define_const vm
      | "pop" -> pop vm
      | "remove" -> remove vm
      | "thm" -> thm vm
      | _ ->
        errorf_ (fun k->k"OT: unknown command %s@." s)
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
  with Error msg -> Error (Format.asprintf "%a" msg ())

let parse_exn (s:string) : article =
  let g = CCString.Split.gen_cpy ~by:"\n" s in
  parse_gen_exn g

let parse s : _ result =
  try Ok (parse_exn s)
  with Error msg -> Error (Format.asprintf "%a" msg())

module Article = struct
  type t = article

  let pp out self =
    Fmt.fprintf out "{@[<hv>article.assumptions=%a;@ theorems=%a@]}"
      (Fmt.Dump.list Thm.pp) self.assumptions
      (Fmt.Dump.list Thm.pp) self.theorems
end
