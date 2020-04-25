module Fmt = CCFormat
module Int_tbl = CCHashtbl.Make(CCInt)
type 'a gen = unit -> 'a option

(* perform more sanity checks *)
let sanity_checks_ = true

module Make(C : Core.S) = struct
  open C.KoT

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
    let equal : t -> t -> bool = (=)
    let hash : t -> int = Hashtbl.hash
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

  module Defs = struct
    module N_tbl = CCHashtbl.Make(Name)
    type t = const N_tbl.t
    let create() : t = N_tbl.create 16
  end

  module N_ty_tbl = CCHashtbl.Make(struct
      type t = string * Expr.t
      let equal = CCEqual.pair String.equal Expr.equal
      let hash = CCHash.pair CCHash.string Expr.hash
  end)

  type article = {
    defs: Defs.t;
    assumptions: thm list;
    theorems: thm list;
  }

  type ty_var = Expr.var
  type vm = {
    vm_ty_vars: (string, ty_var) Hashtbl.t;
    vm_vars: (string, Expr.var * ty_var) Hashtbl.t; (* "x" -> (x, α) *)
    vm_defs: Defs.t;
    mutable vm_stack: obj list;
    vm_dict: obj Int_tbl.t;
    mutable vm_assumptions: thm list;
    mutable vm_theorems: thm list;
  }

  let create ~defs () : vm = {
    vm_ty_vars=Hashtbl.create 16;
    vm_vars=Hashtbl.create 16;
    vm_defs=defs;
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

    (* print with given stack *)
    let pp_with_st out (self, stack) =
      let pp_pair out (i,obj) =
        Fmt.fprintf out "(@[%d :=@ %a@])" i Obj_.pp obj
      in
      Fmt.fprintf out
        "{@[<hv>vm.stack=%a;@ dict=[@[%a@]];@ assumptions=%a;@ theorems=%a@]}"
        (Fmt.Dump.list Obj_.pp) stack
        (Fmt.Dump.list pp_pair) (Int_tbl.to_list self.vm_dict)
        (Fmt.Dump.list Thm.pp) self.vm_assumptions
        (Fmt.Dump.list Thm.pp) self.vm_theorems

    let pp out (self:t) = pp_with_st out (self, self.vm_stack)

    let push_obj self o =
      Fmt.printf "OT.vm.push %a@." Obj_.pp o;
      self.vm_stack <- o :: self.vm_stack

    let pop1 what self f =
      match self.vm_stack with
      | o :: st as old_st ->
        Format.printf "@[<2>%s.pop1:@ %a@]@." what Obj_.pp o;
        self.vm_stack <- st;
        (try f o
         with Error e ->
           error_wrapf_ e
             (fun k->k"in %s using VM.pop1@ with %a" what pp_with_st (self,old_st)))
      | [] ->
        error_ (fun out () -> Fmt.fprintf out "OT.vm.pop1: empty stack@ in %a" pp self)

    let pop2 what self f =
      match self.vm_stack with
      | o1 :: o2 :: st as old_st ->
        Format.printf "@[<2>%s.pop2@ %a;@ %a@]@." what Obj_.pp o1 Obj_.pp o2;
        self.vm_stack <- st;
        (try f (o1,o2)
         with Error e ->
           error_wrapf_ e
             (fun k->k"in %s using VM.pop2@ with %a" what pp_with_st (self,old_st)))
      | [_] | [] ->
        error_ (fun out () -> Fmt.fprintf out "OT.vm.pop2: empty stack@ in %a" pp self)

    let pop3 what self f =
      match self.vm_stack with
      | o1 :: o2 :: o3 :: st as old_st ->
        Format.printf "@[<2>%s.pop3:@ %a;@ %a;@ %a@]@." what Obj_.pp o1 Obj_.pp o2 Obj_.pp o3;
        self.vm_stack <- st;
        (try f (o1,o2,o3)
         with Error e ->
           error_wrapf_ e
             (fun k->k"in %s using VM.pop3 with %a" what pp_with_st (self,old_st)))
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

    (* TODO: replace `\\` by `\` in names *)
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
      VM.pop2 "absTerm" vm @@ function
      | Term t, Var v ->
        VM.push_obj vm @@ Term (Expr.lambda v t)
      | _ ->
        errorf_ (fun k->k"@[<2>OT.abs_term: wrong stack@ in %a@]" VM.pp vm)

    let app_term vm =
      VM.pop2 "appTerm" vm @@ function
      | (Term x, Term f) -> VM.push_obj vm @@ Term (Expr.app f x)
      | _ -> err_bad_stack_ vm "app_term"

    let assume vm =
      VM.pop1 "assume" vm @@ function
          | Term x -> VM.push_obj vm @@ Thm (Thm.assume x)
          | _ -> err_bad_stack_ vm "assume"

    let version vm =
      VM.pop1 "version" vm @@ function
          | Int 6 -> ()
          | Int n -> errorf_ (fun k->k"OT: unsupported version %d" n)
          | _ -> err_bad_stack_ vm "version"

    let axiom vm =
      VM.pop2 "axiom" vm @@ function
        | Term t, List hyps ->
          let hyps = List.map (function Term t -> t | _ -> err_bad_stack_ vm "axiom") hyps in
          let ax, _ = Thm.axiom "_ot_axiom" hyps t in
          Format.printf "@{<Yellow>OT.add-assumption@} %a@." Thm.pp ax;
          vm.vm_assumptions <- ax :: vm.vm_assumptions;
          VM.push_obj vm (Thm ax)
        | _ -> err_bad_stack_ vm "axiom"

    let type_op vm =
      VM.pop1 "typeOp" vm @@ function
      | Name n ->
        begin match n with
          | [], "bool" -> VM.push_obj vm (Type_operator (n,fun [] -> Expr.bool))
          | [], "->" -> VM.push_obj vm (Type_operator (n,fun [a;b] -> Expr.arrow a b))
          | _ -> err_bad_stack_ vm "typeOf"
        end [@warning "-8"]
      | _ -> err_bad_stack_ vm "typeOp"

    let def vm =
      VM.pop2 "def" vm @@ function
      | Int k, x ->
        Int_tbl.replace vm.vm_dict k x;
        VM.push_obj vm x; (* push x back *)
      | _ -> err_bad_stack_ vm "def"

    let cons vm =
      VM.pop2 "cons" vm @@ function
      | List k, x -> VM.push_obj vm (List (x::k))
      | _ -> err_bad_stack_ vm "cons"

    let nil vm = VM.push_obj vm @@ List[]

    let ref_ vm =
      VM.pop1 "ref" vm @@ function
      | Int n ->
        begin match Int_tbl.find vm.vm_dict n with
          | exception Not_found ->
            errorf_ (fun k->k"didn't find object %d in dictionary" n)
          | x -> VM.push_obj vm x
        end
      | _ -> err_bad_stack_ vm "ref"

    let remove vm =
      VM.pop1 "remove" vm @@ function
      | Int n ->
        begin match Int_tbl.find vm.vm_dict n with
          | exception Not_found ->
            errorf_ (fun k->k"didn't find object %d in dictionary" n)
          | x ->
            Int_tbl.remove vm.vm_dict n;
            VM.push_obj vm x
        end
      | _ -> err_bad_stack_ vm "remove"

    let get_ty_var vm (n:name) : Expr.var =
      let n = match n with
        | [], s -> s
        | _ -> errorf_ (fun k->k"bad type variable name %a" Name.debug n)
      in
      match Hashtbl.find vm.vm_ty_vars n with
      | v -> v
      | exception Not_found ->
        let v = Expr.new_var n Expr.type_ in
        Hashtbl.add vm.vm_ty_vars n v;
        v

    let var_type vm =
      VM.pop1 "varType" vm @@ function
      | Name n -> VM.push_obj vm (Type (Expr.var (get_ty_var vm n)))
      | _ -> err_bad_stack_ vm "var_type"

    let op_type vm =
      VM.pop2 "opType" vm @@ function
      | List l, Type_operator (_,f) ->
        let l = List.map
            (function Type t -> t | _ -> errorf_ (fun k->k"expected types")) l in
        VM.push_obj vm (Type (f l))
      | _ -> err_bad_stack_ vm "opType"

    let const vm =
      VM.pop1 "const" vm @@ function
      | Name n  ->
        let c = match n with
          | [], "=" ->
            let c ty =
              match C.unfold_arrow ty with
              | [a;_], _ -> Expr.app Expr.eq_const a
              | _ -> errorf_ (fun k->k"cannot make `=` with type %a" Expr.pp ty)
            in
            c
          | [], "select" ->
            let c ty =
              match C.unfold_arrow ty with
              | [_], a -> Expr.app Expr.select_const a
              | _ -> errorf_ (fun k->k"cannot make `select` with type %a" Expr.pp ty)
            in
            c
          | _ ->
            (try Defs.N_tbl.find vm.vm_defs n
             with Not_found ->
              errorf_ (fun k->k"no constant named %a" Name.debug n))
        in
        VM.push_obj vm (Const (n, c))
      | _ -> err_bad_stack_ vm "const"

    let get_var vm (n:name) ty : Expr.var =
      let n = match n with
        | [], s -> s
        | _ -> errorf_ (fun k->k"bad variable name %a" Name.debug n)
      in
      let v =
        match Hashtbl.find vm.vm_vars n with
        | (v,alpha) ->
          (* reuse [v] but with the given type [ty] *)
          Expr.var_map_ty v (fun ty_v -> Expr.subst1 alpha ty ~in_:ty_v)
        | exception Not_found ->
          let alpha = Expr.new_var "α" Expr.type_ in
          let v = Expr.new_var n (Expr.var alpha) in
          Hashtbl.add vm.vm_vars n (v,alpha);
          Expr.var_map_ty v (fun ty_v -> Expr.subst1 alpha ty ~in_:ty_v)
      in
      assert (Expr.equal (Expr.Var.ty v) ty);
      v

    let var vm =
      VM.pop2 "var" vm @@ function
      | Type ty, Name n ->
        let v = get_var vm n ty in
        VM.push_obj vm (Var v)
      | _ -> err_bad_stack_ vm "var"

    let const_term vm =
      VM.pop2 "constTerm" vm @@ function
      | Type ty, Const (_,c)  ->
        VM.push_obj vm (Term (c ty))
      | _ -> err_bad_stack_ vm "constTerm"

    let var_term vm =
      VM.pop1 "varTerm" vm @@ function
      | Var v -> VM.push_obj vm (Term (Expr.var v))
      | _ -> err_bad_stack_ vm "varTerm"

    let define_const vm =
      VM.pop2 "defineConst" vm @@ function
      | Term t, Name n ->
        (* make a definition [n := t] *)
        let thm, c, vars = C.new_poly_def (Name.to_string n) t in
        Format.printf "@[<2>@{<Yellow>## define const@} %a@ with thm %a@ :vars %a@]@."
          Name.debug n Thm.pp thm (Fmt.Dump.list Expr.Var.pp) vars;
        (* type of [c] applied to [vars] *)
        let c_ty_vars =
          Expr.ty_exn @@ Expr.app_l c (List.map Expr.var vars)
        in
        let mk_c ty =
          let subst =
            try C.unify_exn c_ty_vars ty
            with C.Unif_fail (t1,t2,subst) ->
              errorf_
                (fun k->k"unification failed@ between `%a`@ \
                          and `%a`@ with subst %a"
                    Expr.pp t1 Expr.pp t2 Expr.Subst.pp subst)
          in
          Expr.app_l c
            (List.map
               (fun v -> Expr.Subst.find subst v |> CCOpt.get_or ~default:(Expr.var v))
               vars)
        in
        Defs.N_tbl.add vm.vm_defs n mk_c;
        VM.push_obj vm (Const (n, mk_c));
        VM.push_obj vm (Thm thm);
      | _ -> err_bad_stack_ vm "defineConst"

    let thm vm =
      VM.pop3 "thm" vm @@ function
      | Term _phi, List l, Thm thm ->
        let _l = List.map (function Term t->t | _ -> err_bad_stack_ vm "thm") l in
        (* FIXME: alpha rename with [l] and [phi] *)
        Format.printf "@[<1>@{<Green>## add theorem@}@ %a@ :phi %a@]@."
          Thm.pp thm Expr.pp _phi;
        vm.vm_theorems <- thm :: vm.vm_theorems
      | _ -> err_bad_stack_ vm "thm"

    let refl vm =
      VM.pop1 "refl" vm @@ function
      | Term t -> VM.push_obj vm (Thm (Thm.refl t))
      | _ -> err_bad_stack_ vm "refl"

    let pop vm = VM.pop1 "pop" vm ignore

    let subst vm =
      VM.pop2 "subst" vm @@ function
      | Thm thm, List [List ty_subst; List term_subst] ->
        let ty_subst =
          List.map
            (function
              | List [Name a; Type ty] ->
                get_ty_var vm a, ty (* FIXME: map name->tyvar?*)
              | _ -> err_bad_stack_ vm "subst")
            ty_subst
        and term_subst =
          List.map
            (function
              | List [Var v; Term e] -> v, e
              | _ -> err_bad_stack_ vm "subst")
            term_subst
        in
        let subst = Expr.Subst.of_list (ty_subst @ term_subst) in
        let thm' = Thm.instantiate thm subst in
        Format.printf "(@[instantiate@ %a@ :into %a@ :subst %a@])@."
          Thm.pp thm Thm.pp thm' Expr.Subst.pp subst;
        if sanity_checks_ && Thm.alpha_equiv thm thm' then (
          Format.printf "@{<Red>warning@}: subst gives the same result@.";
        );
        VM.push_obj vm (Thm thm')
      | _ -> err_bad_stack_ vm "subst"

    let abs_thm vm =
      VM.pop2 "absThm" vm @@ function
      | Thm th, Var x ->
        VM.push_obj vm (Thm (Thm.abs x th))
      | _ -> err_bad_stack_ vm "abs_thm"

    let app_thm vm =
      VM.pop2 "appThm" vm @@ function
      | Thm th1, Thm th2 ->
        VM.push_obj vm (Thm (Thm.congr th2 th1))
      | _ -> err_bad_stack_ vm "app_thm"

    let trans vm =
      VM.pop2 "trans" vm @@ function
      | Thm th1, Thm th2 ->
        VM.push_obj vm (Thm (Thm.trans th2 th1))
      | _ -> err_bad_stack_ vm "trans"

    let eq_mp vm =
      VM.pop2 "eqMp" vm @@ function
      | Thm th1, Thm th2 ->
        VM.push_obj vm (Thm (Thm.bool_eq ~eq:th2 th1))
      | _ -> err_bad_stack_ vm "eq_mp"

    let deduct_antisym vm =
      VM.pop2 "deductAntisym" vm @@ function
      | Thm th1, Thm th2 ->
        VM.push_obj vm (Thm (Thm.bool_eq_intro th2 th1))
      | _ -> err_bad_stack_ vm "deduct_antisym"

    let prove_hyp vm =
      VM.pop2 "proveHyp" vm @@ function
      | Thm th1, Thm th2 ->
        VM.push_obj vm (Thm (Thm.cut ~fail_if_not_found:false ~lemma:th1 th2))
      | _ -> err_bad_stack_ vm "prove_hyp"

    let sym vm =
      VM.pop1 "sym" vm @@ function
      | Thm th ->
        VM.push_obj vm (Thm (C.sym th))
      | _ -> err_bad_stack_ vm "sym"

    let beta_conv vm =
      VM.pop1 "betaConv" vm @@ function
      | Term t ->
        VM.push_obj vm (Thm (Thm.beta_conv t))
      | _ -> err_bad_stack_ vm "beta_conv"

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
        | "ref" -> ref_ vm
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
        | "subst" -> subst vm
        | "refl" -> refl vm
        | "trans" -> trans vm
        | "sym" -> sym vm
        | "eqMp" -> eq_mp vm
        | "betaConv" -> beta_conv vm
        | "deductAntisym" -> deduct_antisym vm
        | "proveHyp" -> prove_hyp vm
        | _ ->
          errorf_ (fun k->k"OT: unknown command %s@." s)
      )

    let parse_gen_exn defs (g:string gen) : article =
      let vm = create ~defs () in
      Gen_.iter (process_line vm) @@ cleanup_g g;
      { defs;
        assumptions= vm.vm_assumptions;
        theorems= vm.vm_theorems;
      }
  end

  let parse_gen_exn = Parse_.parse_gen_exn

  let parse_gen defs g : _ result =
    try Ok (parse_gen_exn defs g)
    with Error msg -> Error (Format.asprintf "%a" msg ())

  let parse_exn defs (s:string) : article =
    let g = CCString.Split.gen_cpy ~by:"\n" s in
    parse_gen_exn defs g

  let parse defs s : _ result =
    try Ok (parse_exn defs s)
    with Error msg -> Error (Format.asprintf "%a" msg())

  module Article = struct
    type t = article

    let pp out self =
      Fmt.fprintf out "{@[<hv>article.assumptions=%a;@ theorems=%a@]}"
        (Fmt.Dump.list Thm.pp) self.assumptions
        (Fmt.Dump.list Thm.pp) self.theorems
  end
end
