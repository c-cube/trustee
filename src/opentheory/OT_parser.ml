
module K = Trustee_core.Kernel
module Log = Trustee_core.Log
module Unif = Trustee_core.Unif

type input = {
  iter_lines: string Iter.t;
}

module Input = struct
  type t = input

  let rec iter_g f g = match g() with
    | None -> ()
    | Some s -> f s; iter_g f g

  let of_string s : t  =
    let iter_lines = CCString.Split.iter_cpy ~by:"\n" s in
    {iter_lines}

  let of_chan ic =
    let iter_lines = fun yield -> iter_g yield (CCIO.read_lines_gen ic) in
    {iter_lines}

  (* TODO: camlzip: dezip + of_string *)
end

let unescape s : string =
  let n = String.length s in
  let buf = Buffer.create (String.length s) in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    match c with
    | '\\' when !i + 1 < n ->
      begin match s.[!i+1] with
        | 'n' -> Buffer.add_char buf '\n'; i := !i + 2
        | '"' -> Buffer.add_char buf '"'; i := !i + 2
        | '\\' -> Buffer.add_char buf '\\'; i := !i + 2
        | _ -> Buffer.add_char buf c; incr i
      end;
    | _ -> Buffer.add_char buf c; incr i
  done;
  Buffer.contents buf

module Name = struct
  type t = {
    path: string list;
    name: string;
  }

  let of_string s : t =
    let s = unescape s in
    match CCString.split_on_char '.' s with
    | [name] -> {path=[]; name}
    | [] -> errorf (fun k->k"invalid name: '%s'" s)
    | l ->
      let name = List.hd @@ CCList.last 1 l in
      let path = CCList.take (List.length l-1) l in
      {path; name}

  let to_string (self:t) =
    match self.path with
    | [] -> self.name
    | ps -> String.concat "." ps ^ "." ^ self.name
  let pp out self = Fmt.string out (to_string self)
end

module Article = struct
  type t = {
    consts: K.Const.t list;
    axioms: K.Thm.t list;
    theorems: K.Thm.t list;
  }

  let empty : t = { axioms=[]; theorems=[]; consts=[]; }

  type item =
    | I_cst of K.Const.t
    | I_axiom of K.Thm.t
    | I_thm of K.Thm.t

  let items self =
    Iter.append_l [
      Iter.of_list self.consts |> Iter.map (fun c->I_cst c);
      Iter.of_list self.axioms |> Iter.map (fun th->I_axiom th);
      Iter.of_list self.theorems |> Iter.map (fun th->I_thm th);
    ]

  let pp_stats out (self:t) : unit =
    Fmt.fprintf out "(@[%d consts, %d assumptions, %d theorems@])"
      (List.length self.consts) (List.length self.axioms) (List.length self.theorems)

  let pp_item out = function
    | I_cst c -> Fmt.fprintf out "(@[const %a@])" K.Const.pp c
    | I_axiom th -> Fmt.fprintf out "(@[axiom %a@])" K.Thm.pp_quoted th
    | I_thm th -> Fmt.fprintf out "(@[theorem %a@])" K.Thm.pp_quoted th

  let pp out (self:t) =
    Fmt.fprintf out "@[<v2>art {@,%a@;<1 -4>}@]"
      (Fmt.iter pp_item) (items self)
  let to_string = Fmt.to_string pp
end

module VM = struct
  type ty_op = Name.t * (K.ctx -> K.ty list -> K.ty)
  type const = Name.t * (K.ctx -> K.ty -> K.expr)

  type obj =
    | O_int of int
    | O_name of Name.t
    | O_ty of K.ty
    | O_ty_op of ty_op
    | O_const of const
    | O_var of K.var
    | O_term of K.expr
    | O_thm of K.thm
    | O_list of obj list

  let rec pp_obj out = function
    | O_int i -> Fmt.int out i
    | O_name n -> Name.pp out n
    | O_ty ty -> Fmt.fprintf out "(@[ty: %a@])" K.Expr.pp ty
    | O_ty_op (c,_) -> Fmt.fprintf out "(@[ty-const: %a@])" Name.pp c
    | O_const (c,_) -> Fmt.fprintf out "(@[const: %a@])" Name.pp c
    | O_var v -> Fmt.fprintf out "(@[var: %a@])" K.Var.pp v
    | O_term e -> Fmt.fprintf out "(@[term: %a@])" K.Expr.pp e
    | O_thm th -> Fmt.fprintf out "(@[thm: %a@])" K.Thm.pp_quoted th
    | O_list l -> Fmt.Dump.list pp_obj out l

  type t = {
    ctx: K.ctx;
    mutable stack: obj list;
    dict: (int, obj) Hashtbl.t;
    mutable named_consts: (Name.t, const) Hashtbl.t;
    mutable named_tys: (Name.t, ty_op) Hashtbl.t;
    mutable art: Article.t;
    ind: K.const;

    mutable n_absThm : int;
    mutable n_appThm : int;
    mutable n_cut : int
  }

  let article (self:t) : Article.t = self.art
  let clear_article self = self.art <- Article.empty
  let clear_dict self = Hashtbl.clear self.dict

  let pp_stack out self =
    Fmt.fprintf out "[@[<hv>%a@]]"
      Fmt.(list ~sep:(return ";@ ") pp_obj) self.stack

  let pp_vm out (self:t) : unit =
    Fmt.fprintf out "{@[stack:@ %a;@ dict={@[<hv>%a@]}@]}"
      pp_stack self
      (Fmt.iter Fmt.Dump.(pair int pp_obj)) (CCHashtbl.to_iter self.dict)

  let pp out self : unit =
    Fmt.fprintf out "{@[vm:@ %a;@ art: %a@]}"
      pp_vm self Article.pp (article self)

  let pp_stats out self : unit =
    Fmt.fprintf out "(@[:n-cuts %d :n-absThm %d@ :n-appThm %d@])"
      self.n_cut self.n_absThm self.n_appThm

  let to_string = Fmt.to_string pp

  (* a rule associated with a keyword *)
  type rule = t -> unit

  let version : rule = fun self ->
    match self.stack with
    | O_int (5 | 6) :: st -> self.stack <- st
    | O_int n :: _ -> errorf (fun k->k"expected version to be '5' or '6', not %d" n)
    | _ -> errorf (fun k->k"version: expected an integer")

  let absTerm : rule = fun self ->
    match self.stack with
    | O_term b :: O_var v :: st ->
      let t = K.Expr.lambda self.ctx v b in
      self.stack <- O_term t :: st;
    | _ -> errorf (fun k->k"cannot apply absTerm@ in state %a" pp_vm self)

  let absThm : rule = fun self ->
    self.n_absThm <- 1 + self.n_absThm;
    match self.stack with
    | O_thm th :: O_var v :: st ->
      let th = K.Thm.abs self.ctx th v in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply absThm@ in state %a" pp_vm self)

  let typeOp : rule = fun self ->
    match self.stack with
    | O_name n :: st ->
      let f_op = match n with
        | {Name.path=[];name="->"} ->
          (fun ctx -> function
             | [a;b] -> K.Expr.arrow ctx a b
             | _ -> error "arrow expects 2 args")
        | {Name.path=[];name="bool"} ->
          (fun ctx -> function [] -> K.Expr.bool ctx | _ -> error "bool is a const")
        | {Name.path=[];name="ind"} ->
          (fun ctx -> function
             | [] -> K.Expr.const ctx self.ind [] | _ -> error "ind is a const")
        | _ ->
          try snd @@ Hashtbl.find self.named_tys n
          with Not_found ->
            errorf (fun k->k"unknown type operator '%a'" Name.pp n)
      in
      let op = n, f_op in
      self.stack <- O_ty_op op :: st;
    | _ -> errorf (fun k->k"cannot apply typeOp@ in state %a" pp_vm self)

  let def : rule = fun self ->
    match self.stack with
    | O_int i :: x :: st ->
      self.stack <- x :: st;
      Hashtbl.replace self.dict i x
    | _ -> errorf (fun k->k"cannot apply def@ in state %a" pp_vm self)

  let varType : rule = fun self ->
    match self.stack with
    | O_name {Name.path=[]; name=s} :: st ->
      let v = K.Var.make s (K.Expr.type_ self.ctx) in
      self.stack <- O_ty (K.Expr.var self.ctx v) :: st;
    | _ -> errorf (fun k->k"cannot apply varType@ in state %a" pp_vm self)

  let nil : rule = fun self -> self.stack <- O_list [] :: self.stack

  let cons : rule = fun self ->
    match self.stack with
    | O_list l :: o :: st ->
      self.stack <- O_list (o::l) :: st
    | _ -> errorf (fun k->k"cannot apply cons@ in state %a" pp_vm self)

  let opType : rule = fun self ->
    match self.stack with
    | O_list l :: O_ty_op (_,op) :: st ->
      let args = l |> List.map (function
          | O_ty ty -> ty
          | o -> errorf (fun k->k"typeOp: %a is not a type" pp_obj o))
      in
      let ty = op self.ctx args in
      self.stack <- O_ty ty :: st;
    | _ -> errorf (fun k->k"cannot apply typeOp@ in state %a" pp_vm self)

  let var : rule = fun self ->
    match self.stack with
    | O_ty ty :: O_name {Name.path=[];name=n} :: st ->
      let v = K.Var.make n ty in
      self.stack <- O_var v :: st
    | _ -> errorf (fun k->k"cannot apply var@ in state %a" pp_vm self)

  let const : rule = fun self ->
    match self.stack with
    | O_name n :: st ->
      let f_op = match n with
        | {Name.path=[]; name="="} ->
          (fun ctx ty ->
             match K.Expr.view ty with
             | K.Expr.E_arrow (a, _) -> K.Expr.eq ctx a
             | _ -> error "= has an arrow type")
        | {Name.path=[]; name="select"} ->
          (fun ctx ty ->
             match K.Expr.view ty with
             | K.Expr.E_arrow (_, a) -> K.Expr.select ctx a
             | _ -> error "select has an arrow type")
        | _ ->
          begin match Hashtbl.find self.named_consts n with
            | _, c -> c
            | exception Not_found ->
              errorf (fun k->k"unknown const '%a'" Name.pp n)
          end
      in
      self.stack <- O_const (n, f_op) :: st
    | _ -> errorf (fun k->k"cannot apply const@ in state %a" pp_vm self)

  let ref_ : rule = fun self ->
    match self.stack with
    | O_int i :: st ->
      (try self.stack <- Hashtbl.find self.dict i :: st
       with Not_found -> errorf (fun k->k"undefined ref %d" i))
    | _ -> errorf (fun k->k"cannot apply ref@ in state %a" pp_vm self)

  let constTerm : rule = fun self ->
    match self.stack with
    | O_ty ty :: O_const (_,c) :: st ->
      let t = c self.ctx ty in
      self.stack <- O_term t :: st
    | _ -> errorf (fun k->k"cannot apply constTerm@ in state %a" pp_vm self)

  let varTerm : rule = fun self ->
    match self.stack with
    | O_var v :: st ->
      let t = K.Expr.var self.ctx v in
      self.stack <- O_term t :: st
    | _ -> errorf (fun k->k"cannot apply varTerm@ in state %a" pp_vm self)

  (* FIXME: move polymorphic apply/congr to the kernel itself? (also implement it for congr) *)
  let appTerm : rule = fun self ->
    match self.stack with
    | O_term a :: O_term f :: st ->
      (*Log.debugf 10 (fun k->k"appterm `%a : %a`@ to `%a : %a`"
                        K.Expr.pp f K.Expr.pp (K.Expr.ty_exn f)
                        K.Expr.pp a K.Expr.pp (K.Expr.ty_exn a));*)
      let t = K.Expr.app self.ctx f a in
      self.stack <- O_term t :: st
    | _ -> errorf (fun k->k"cannot apply appTerm@ in state %a" pp_vm self)

  (* create a defined constant, with local type inference since OT
     gives us only the expected type of the constant *)
  let mk_defined_const_ c =
    match K.Const.args c with
    | K.Const.C_arity _ -> errorf (fun k->k"not a term const: %a" K.Const.pp c)
    | K.Const.C_ty_vars [] ->
      (* non-polymorphic constant *)
      (fun ctx _ty -> assert (K.Var.Set.is_empty @@ K.Expr.free_vars _ty); K.Expr.const ctx c [])
    | K.Const.C_ty_vars ty_vars ->
      (* make new variables *)
      let vars =
        List.mapi (fun i v -> K.Var.makef "√%d" (K.Var.ty v) i) ty_vars in
      (fun ctx ty ->
        let e = K.Expr.const ctx c (List.map (K.Expr.var ctx) vars) in
        let ty_e = K.Expr.ty_exn e in
        match Unif.match_ ty_e ty with
        | None ->
          errorf (fun k->k"type %a@ does not match type of %a"
                     K.Expr.pp ty K.Expr.pp e)
        | Some subst -> K.Expr.subst ctx e subst
      )

  let define_named_ ctx n t : K.Thm.t * K.const =
    let s = Name.to_string n in
    let eqn =
      K.Expr.(app_eq ctx
                (var ctx (K.Var.make s (ty_exn t))) t)
    in
    let th, c = K.Thm.new_basic_definition ctx eqn in
    th, c

  let defineConst : rule = fun self ->
    match self.stack with
    | O_term t :: O_name n :: st ->
      if Hashtbl.mem self.named_consts n then (
        errorf (fun k->k"a constant %a is already defined" Name.pp n);
      );
      let th, c = define_named_ self.ctx n t in
      self.art <- {self.art with Article.consts=c :: self.art.Article.consts};
      let c = mk_defined_const_ c in
      Hashtbl.add self.named_consts n (n,c);
      self.stack <- O_thm th :: O_const (n, c) :: st
    | _ -> errorf (fun k->k"cannot apply defineConst@ in state %a" pp_vm self)

  let defineConstList : rule = fun self ->
    match self.stack with
    | O_thm th :: O_list l :: st ->
      let hyps = K.Thm.hyps_l th in
      let concl = K.Thm.concl th in

      let names =
        List.map
          (function O_list [O_name n; O_var v] -> n,v
                  | _ -> errorf (fun k->k"expected list of (name,var)"))
          l
      in

      let vars = List.map snd names |> K.Var.Set.of_list in

      (* free variables of the RHS (excluding type vars) *)
      let fvars_concl =
        K.Expr.free_vars_iter concl
        |> Iter.filter (fun v -> not (K.Expr.is_eq_to_type (K.Var.ty v)))
        |> K.Var.Set.of_iter
      in
      if not (K.Var.Set.subset fvars_concl vars) then (
        Log.debugf 2 (fun k->k"thm: %a" K.Thm.pp th);
        errorf
          (fun k->k"defineConstList: some free vars are not in hypothesis@ \
                    :fvars-concl %a@ :vars %a"
              Fmt.(Dump.list K.Var.pp) (K.Var.Set.to_list fvars_concl)
              Fmt.(Dump.list K.Var.pp) (K.Var.Set.to_list vars)
          );
      );

      (* decompose hypothesis as [v = rhs] pairs *)
      let hyps_as_vars =
        List.map
          (fun hyp -> match K.Expr.unfold_eq hyp with
             | Some (v, rhs) ->
               begin match K.Expr.view v with
                 | K.Expr.E_var v -> v, rhs
                 | _ -> error "expected hypothesis to have variable as LHS"
               end
             | _ -> error "expected hypothesis to be an equation")
          hyps
      in

      let subst, (thms,consts) =
        CCList.fold_map
          (fun subst (n,v) ->
            let rhs =
              try CCList.assoc ~eq:K.Var.equal v hyps_as_vars
              with Not_found ->
                errorf(fun k->k"cannot find hypothesis with var `%a`" K.Var.pp v)
            in

            let th, c = define_named_ self.ctx n rhs in
            self.art <- {self.art with Article.consts=c :: self.art.Article.consts};
            let c' = (n,mk_defined_const_ c) in
            Hashtbl.add self.named_consts n c';

            (* add [v := c] to the substitution *)
            let c_inst = (snd c') self.ctx (K.Var.ty v) in
            let subst = K.Subst.bind v c_inst subst in

            subst, (th,c'))
          K.Subst.empty names
          |> CCPair.map_snd List.split
      in

      (* instantiate theorem, and cut to remove the constant definition theorems *)
      let th = K.Thm.subst self.ctx th subst in
      let th =
        List.fold_left
          (fun th th' -> K.Thm.cut self.ctx th' th) th thms
      in
      Log.debugf 10 (fun k->k"(@[defineConstList.result@ %a@])" K.Thm.pp th);

      self.stack <- O_thm th :: O_list (List.map (fun c->O_const c) consts) :: st
    | _ -> errorf (fun k->k"cannot apply defineConst@ in state %a" pp_vm self)

  let pop : rule = fun self ->
    match self.stack with
    | _ :: st -> self.stack <- st
    | [] -> errorf (fun k->k"cannot apply pop@ in state %a" pp_vm self)

  let remove : rule = fun self ->
    match self.stack with
    | O_int i :: st ->
      let o =
        (try Hashtbl.find self.dict i
         with Not_found -> errorf (fun k->k"key %d not defined" i))
      in
      Hashtbl.remove self.dict i;
      self.stack <- o :: st
    | _ -> errorf (fun k->k"cannot apply pop@ in state %a" pp_vm self)

  let thm : rule = fun self ->
    match self.stack with
    | O_term _ :: O_list _ :: O_thm th :: st ->
      self.stack <- st; (* note: we skip the alpha renaming because of DB indices *)
      self.art <- {self.art with Article.theorems = th :: self.art.Article.theorems};
    | _ -> errorf (fun k->k"cannot apply thm@ in state %a" pp_vm self)

  let refl : rule = fun self ->
    match self.stack with
    | O_term t :: st ->
      let th = K.Thm.refl self.ctx t in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply refl@ in state %a" pp_vm self)

  let betaConv : rule = fun self ->
    match self.stack with
    | O_term t :: st ->
      let th = K.Thm.beta_conv self.ctx t in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply betaConv@ in state %a" pp_vm self)

  let axiom : rule = fun self ->
    match self.stack with
    | O_term t :: O_list _ :: st ->
      (* we ignore the renaming list *)
      let th = K.Thm.axiom self.ctx t in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply axiom@ in state %a" pp_vm self)

  let appThm : rule = fun self ->
    self.n_appThm <- 1 + self.n_appThm;
    match self.stack with
    | O_thm a :: O_thm f :: st ->
      (* Log.debugf 10 (fun k->k"appThm `%a` `%a`" K.Thm.pp f K.Thm.pp a); *)
      let th = K.Thm.congr self.ctx f a in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply appThm@ in state %a" pp_vm self)

  let eqMp : rule = fun self ->
    match self.stack with
    | O_thm a :: O_thm f :: st ->
      let th = K.Thm.bool_eq self.ctx a f in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply eqMp@ in state %a" pp_vm self)

  let sym : rule = fun self ->
    match self.stack with
    | O_thm th :: st ->
      let th = K.Thm.sym self.ctx th in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply sym@ in state %a" pp_vm self)

  let subst : rule = fun self ->
    match self.stack with
    | O_thm th :: O_list [O_list tys; O_list terms] :: st ->
      let subst =
        List.fold_left
          (fun subst p -> match p with
             | O_list [O_name {Name.path=[]; name=s}; O_ty ty] ->
               let var = K.Var.make s (K.Expr.type_ self.ctx) in
               K.Subst.bind var ty subst
             | _ -> errorf (fun k->k"expect first list to be a type subst"))
          K.Subst.empty tys
      in
      let subst =
        List.fold_left
          (fun subst p -> match p with
             | O_list [O_var v; O_term e] ->
               Log.debugf 50 (fun k->k"v=%a; t=`%a`; ty(t)=`%a` same-ty=%B"
                                 K.Var.pp_with_ty v K.Expr.pp e K.Expr.pp (K.Expr.ty_exn e)
                                 (K.Expr.equal (K.Var.ty v) (K.Expr.ty_exn e)));
               K.Subst.bind v e subst
             | _ -> errorf (fun k->k"expect second list to be an expr subst"))
          subst terms
      in
      let th = K.Thm.subst self.ctx th subst in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply subst@ in state %a" pp_vm self)

  let assume : rule = fun self ->
    match self.stack with
    | O_term e :: st ->
      let th = K.Thm.assume self.ctx e in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply assume@ in state %a" pp_vm self)

  let deductAntisym : rule = fun self ->
    match self.stack with
    | O_thm th1 :: O_thm th2 :: st ->
      let th = K.Thm.bool_eq_intro self.ctx th2 th1 in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply deductAntisym@ in state %a" pp_vm self)

  let trans : rule = fun self ->
    match self.stack with
    | O_thm th1 :: O_thm th2 :: st ->
      let th = K.Thm.trans self.ctx th2 th1 in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply trans@ in state %a" pp_vm self)

  let proveHyp : rule = fun self ->
    self.n_cut <- 1 + self.n_cut;
    match self.stack with
    | O_thm th2 :: O_thm th1 :: st ->
      let th = K.Thm.cut self.ctx th1 th2 in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply proveHyp@ in state %a" pp_vm self)

  (* create a defined constant, with local type inference since OT
     gives us only the expected type of the constant *)
  let mk_defined_ty_ c =
    match K.Const.args c with
    | K.Const.C_arity 0 ->
      (* non-polymorphic constant *)
      (fun ctx _ty -> assert (_ty=[]); K.Expr.const ctx c [])
    | K.Const.C_arity n ->
      (fun ctx _tyargs -> assert (List.length _tyargs=n); K.Expr.const ctx c _tyargs)
    | K.Const.C_ty_vars _ ->
      errorf (fun k->k"not a type const: %a" K.Const.pp c)

  let defineTypeOp : rule = fun self ->
    match self.stack with
    | O_thm th :: O_list names :: O_name rep :: O_name abs :: O_name tau :: st ->
      (* TODO: check names? *)
      let ty_vars =
        List.map
          (function
            | O_name {path=[];name} -> K.Var.make name (K.Expr.type_ self.ctx)
            | _ -> errorf (fun k->k"expect a list of names"))
          names
      in
      let def =
        K.Thm.new_basic_type_definition self.ctx
          ~ty_vars
          ~name:(Name.to_string tau) ~abs:(Name.to_string abs)
          ~repr:(Name.to_string rep) ~thm_inhabited:th
          ()
      in
      let c_abs = (abs, mk_defined_const_ def.c_abs) in
      self.art <- {self.art with Article.consts=def.c_abs :: self.art.Article.consts};
      Hashtbl.add self.named_consts abs c_abs;
      self.art <- {self.art with Article.consts=def.c_repr :: self.art.Article.consts};
      let c_rep = (rep, mk_defined_const_ def.c_repr) in
      Hashtbl.add self.named_consts rep c_rep;
      self.art <- {self.art with Article.consts=def.tau :: self.art.Article.consts};
      let c_tau = (tau, mk_defined_ty_ def.tau) in
      Hashtbl.add self.named_tys tau c_tau;

      (* need to abstract over the theorems *)
      let repr_thm =
        let th = K.Thm.sym self.ctx def.repr_thm in (* flip first *)
        K.Thm.abs self.ctx th def.repr_x in
      let abs_thm = K.Thm.abs self.ctx def.abs_thm def.abs_x in

      self.stack <-
        O_thm repr_thm ::
        O_thm abs_thm ::
        O_const c_rep ::
        O_const c_abs ::
        O_ty_op c_tau ::
        st;
    | _ -> errorf (fun k->k"cannot apply defineTypeOp@ in state %a" pp_vm self)

  let hdTl : rule = fun self ->
    match self.stack with
    | O_list (x::tl) :: st ->
      self.stack <- O_list tl :: x :: st;
    | _ -> errorf (fun k->k"cannot apply hdTl@ in state %a" pp_vm self)

  let rules : rule Str_map.t = [
    "version", version;
    "absTerm", absTerm;
    "absThm", absThm;
    "typeOp", typeOp;
    "def", def;
    "varType", varType;
    "nil", nil;
    "cons", cons;
    "opType", opType;
    "var", var;
    "const", const;
    "ref", ref_;
    "constTerm", constTerm;
    "varTerm", varTerm;
    "appTerm", appTerm;
    "defineConst", defineConst;
    "pop", pop;
    "remove", remove;
    "thm", thm;
    "refl", refl;
    "betaConv", betaConv;
    "axiom", axiom;
    "appThm", appThm;
    "eqMp", eqMp;
    "sym", sym;
    "subst", subst;
    "assume", assume;
    "deductAntisym", deductAntisym;
    "trans", trans;
    "proveHyp", proveHyp;
    "defineTypeOp", defineTypeOp;
    "defineConstList", defineConstList;
    "hdTl", hdTl;
  ] |> Str_map.of_list

  let create ctx : t =
    let ind = K.Expr.new_ty_const ctx "ind" 0 in (* special type *)
    let self = {
      ctx; stack=[]; dict=Hashtbl.create 32; named_consts=Hashtbl.create 32;
      named_tys=Hashtbl.create 16;
      art=Article.empty; ind;
      n_cut=0; n_appThm=0; n_absThm=0;
    } in
    self

  let has_empty_stack self =
    match self.stack with [] -> true | _ -> false

  let parse_and_check_art_exn (self:t) (input:input) : Article.t =
    Log.debug 5 "(open-theory.parse-and-check-art)";
    let i = ref 0 in

    (* how to parse one line *)
    let process_line (s:string) : unit =
      incr i;

      let s = String.trim s in
      if s="" then errorf (fun k->k"empty line (at line %d)" !i);

      Log.debugf 50 (fun k->k"(@[ot: cur VM stack is@ %a@])" pp_stack self);
      Log.debugf 20 (fun k->k"(@[ot: process line: %s@])" s);

      begin match s.[0] with
        | '0' .. '9' | '-' ->
          let n =
            (try int_of_string s
             with _ -> errorf (fun k->k"invalid integer at line %d" !i))
          in
          self.stack <- O_int n :: self.stack
        | '"' ->
          let n = String.length s in
          if s.[n-1] <> '"' then errorf (fun k->k"expected closing \" at line %d" !i);
          let s = String.sub s 1 (n-2) in
          let n = Name.of_string s in
          self.stack <- O_name n :: self.stack
        | _ ->
          begin match Str_map.find s rules with
            | r -> r self
            | exception Not_found ->
              errorf (fun k->k"unknown rule '%s' at line %d" s !i)
          end
      end;
    in
    input.iter_lines process_line;
    let art = article self in
    self.art <- Article.empty; (* clear article for next file, if any *)
    art

  let parse_and_check_art self i =
    try Ok (parse_and_check_art_exn self i)
    with Trustee_error.E e -> Error e
end

let parse_and_check_art ctx i =
  let st = VM.create ctx in
  VM.parse_and_check_art st i

