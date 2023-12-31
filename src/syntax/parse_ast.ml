open Common_

type fixity = Fixity.t

type 'a with_loc = 'a With_loc.t = {
  loc: Loc.t;
  view: 'a;
}

(** A constant, with location. *)
module Const = struct
  type t = string with_loc

  let make ~loc (name : string) : t = { view = name; loc }

  let pp out (self : t) = Fmt.string out self.view

  let name (self : t) : string = self.view

  let loc (self : t) = self.loc

  let bool : t = make ~loc:Loc.none "bool"
end

(** A variable, bound or free.

    Typically its name is local and non qualified. *)
module Var = struct
  type var_kind =
    | V_normal
    | V_at
    | V_question_mark

  type 'ty t = {
    name: string;
    ty: 'ty option;
    kind: var_kind;
    loc: Loc.t;
  }

  let make ?(kind = V_normal) ~loc name ty : _ t = { name; ty; kind; loc }

  let pp out v = Fmt.string out v.name

  let to_string v = Fmt.to_string pp v

  let pp_with_ty ppty out self =
    match self.ty with
    | None -> Fmt.string out self.name
    | Some ty -> Fmt.fprintf out "[@[%s@ %a@]]" self.name ppty ty
end

(** A logical expression. *)
module Expr = struct
  type t = view with_loc

  and ty = t

  and var = ty Var.t

  and binding = var * t

  and view =
    | Type
    | Ty_arrow of ty list * ty
    | Var of var
    | Meta of {
        name: string;
        ty: ty option;
      }
    | Wildcard
    | App of t * t list
    | Lambda of var list * t
    | Bind of {
        b: Const.t;
        vars: var list;
        body: t;
      }
    | Eq of t * t
    | With of var list * t
    | Let of binding list * t
    | Error of Error.t

  let unfold_app e : t * t list =
    let rec aux acc e =
      match e.view with
      | App (f, a) -> aux (a @ acc) f
      | _ -> e, acc
    in
    aux [] e

  let rec pp_sexp out (e : t) : unit =
    match e.view with
    | Type -> Fmt.string out "type"
    | Var v -> Var.pp out v
    | Ty_arrow (a, b) ->
      Fmt.fprintf out "(@[->@ %a@ %a@])" (pp_list pp_sexp) a pp_sexp b
    | App _ ->
      let f, args = unfold_app e in
      Fmt.fprintf out "(@[%a@ %a@])" pp_sexp f (pp_list pp_sexp) args
    | Meta v -> Fmt.fprintf out "?%s" v.name
    | Lambda (vars, bod) ->
      Fmt.fprintf out "(@[lambda (@[%a@])@ %a@])" (pp_list pp_var_ty) vars
        pp_sexp bod
    | Bind { b; vars; body } ->
      Fmt.fprintf out "(@[%a@ (@[lambda (@[%a@])@ %a@])@])" Const.pp b
        (pp_list pp_var_ty) vars pp_sexp body
    | With (vars, bod) ->
      Fmt.fprintf out "(@[with (@[%a@])@ %a@])" (pp_list pp_var_ty) vars pp_sexp
        bod
    | Eq (a, b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp_sexp a pp_sexp b
    | Wildcard -> Fmt.string out "_"
    | Let (bs, bod) ->
      let pp_binding out (x, e) =
        Fmt.fprintf out "[@[%a@ %a@]]" Var.pp x pp_sexp e
      in
      Fmt.fprintf out "(@[let@ (@[%a@])@ %a@])" (pp_list pp_binding) bs pp_sexp
        bod
    | Error err -> Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  and pp_var_ty out v = Var.pp_with_ty pp_sexp out v

  let pp out e = Fmt.fprintf out "@[%a@]" pp_sexp e

  let mk_ ~loc view : t = { view; loc }

  let[@inline] view e = e.view

  let[@inline] loc e = e.loc

  let pp_quoted = Fmt.within "`" "`" @@ pp

  let type_ : t = mk_ ~loc:Loc.none Type

  let ty_var ~loc s : t = mk_ ~loc (Var (Var.make ~loc s (Some type_)))

  let ty_meta ~loc (s : string) : ty =
    mk_ ~loc (Meta { ty = Some type_; name = s })

  let ty_arrow ~loc a b : ty = mk_ ~loc (Ty_arrow (a, b))

  let var ~loc (v : var) : t = mk_ ~loc (Var v)

  let var' ~loc v ty : t = var ~loc (Var.make ~loc v ty)

  let bool : t = var' ~loc:Loc.none "bool" (Some type_)

  let meta ~loc (s : string) ty : t = mk_ ~loc (Meta { ty; name = s })

  let app (f : t) (args : t list) : t =
    if args = [] then
      f
    else
      mk_ ~loc:Loc.(union_l f.loc ~f:(fun e -> e.loc) args) (App (f, args))

  let let_ ~loc bs bod : t = mk_ ~loc (Let (bs, bod))

  let with_ ~loc vs bod : t = mk_ ~loc (With (vs, bod))

  let lambda ~loc vs bod : t = mk_ ~loc (Lambda (vs, bod))

  let bind ~loc b vars body : t = mk_ ~loc (Bind { b; vars; body })

  let eq ~loc a b : t = mk_ ~loc (Eq (a, b))

  let wildcard ~loc () : t = mk_ ~loc Wildcard

  let error ~loc err : t = mk_ ~loc (Error err)

  let to_string = Fmt.to_string @@ Fmt.hvbox pp

  let rec iter_errors yield e =
    let recurse e = iter_errors yield e in
    let recurse_v v = Option.iter recurse v.Var.ty in
    match view e with
    | Type | Wildcard -> ()
    | Var v -> recurse_v v
    | Ty_arrow (args, ret) ->
      List.iter recurse args;
      recurse ret
    | Meta { ty; _ } -> Option.iter recurse ty
    | App (f, args) ->
      recurse f;
      List.iter recurse args
    | Lambda (vs, bod) ->
      List.iter recurse_v vs;
      recurse bod
    | Bind { vars; body; _ } ->
      List.iter recurse_v vars;
      recurse body
    | Eq (a, b) ->
      recurse a;
      recurse b
    | With (vs, b) ->
      List.iter recurse_v vs;
      recurse b
    | Let (bs, bod) ->
      recurse bod;
      List.iter
        (fun (v, t) ->
          recurse_v v;
          recurse t)
        bs
    | Error err -> yield (e.loc, err)

  let error_set (e : t) : Error_set.t =
    object
      method iter_errors k = iter_errors k e
    end
end

(** A logical substitution literal. *)
module Subst = struct
  type t = (Expr.var * Expr.t) list with_loc

  let mk_ ~loc view : t = { view; loc }

  let pp out (s : t) =
    let pppair out (v, e) = Fmt.fprintf out "(@[%a %a@])" Var.pp v Expr.pp e in
    Fmt.fprintf out "(@[subst@ %a@])" (pp_list ~sep:"," pppair) s.view

  let to_string = Fmt.to_string pp
end

(** A goal, ie. a sequent to prove. *)
module Goal = struct
  type t = view with_loc

  and view =
    | Goal of {
        new_vars: Expr.var list;
        hyps: Expr.t list;
        concl: Expr.t;
      }
    | Error of Error.t

  let[@inline] mk ~loc view : t = { loc; view }

  let[@inline] view self = self.view

  let[@inline] loc self = self.loc

  let goal ~loc ?(new_vars = []) ~hyps concl : t =
    mk ~loc @@ Goal { hyps; concl; new_vars }

  let goal_nohyps ~loc c : t = goal ~loc ~hyps:[] c

  let error ~loc err : t = mk ~loc @@ Error err

  let pp out (self : t) =
    let pp_newvar out v = Fmt.fprintf out "(@[new@ %a@])@," Expr.pp_var_ty v
    and pp_hyp out e = Fmt.fprintf out "(@[assume@ %a@])@," Expr.pp e in
    match self.view with
    | Goal { new_vars = []; hyps = []; concl } -> Expr.pp out concl
    | Goal { new_vars; hyps; concl } ->
      Fmt.fprintf out "(@[<hv>goal@ %a%a(@[prove@ %a@])@])" (pp_list pp_newvar)
        new_vars (pp_list pp_hyp) hyps Expr.pp concl
    | Error e -> Fmt.fprintf out "<@[error@ %a@]>" Error.pp e

  let to_string = Fmt.to_string pp

  let iter_errors f (self : t) =
    match view self with
    | Goal { new_vars; hyps; concl } ->
      let recurse_e = Expr.iter_errors f in
      List.iter (fun v -> Option.iter recurse_e v.Var.ty) new_vars;
      List.iter recurse_e hyps;
      recurse_e concl
    | Error err -> f (self.loc, err)
end

(** A type in the meta language. *)
module Meta_ty = struct
  type t = view with_loc

  and view =
    | Const of Const.t
    | Arrow of t list * t
    | Error of Error.t

  let[@inline] mk ~loc view : t = { view; loc }

  let[@inline] loc self = self.loc

  let[@inline] view self = self.view

  let rec pp out (self : t) =
    match self.view with
    | Const c -> Const.pp out c
    | Arrow (args, ret) ->
      Fmt.fprintf out "(@[->@ %a@ %a@])" (pp_list pp) args pp ret
    | Error err -> Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  let const c : t = mk ~loc:c.loc (Const c)

  let const_str ~loc s : t = const (Const.make ~loc s)

  let arrow args ret =
    match args with
    | [] -> ret
    | _ ->
      let loc = Loc.(union_l ret.loc ~f:loc args) in
      mk ~loc (Arrow (args, ret))

  let rec iter_errors f (self : t) : unit =
    let recurse e = iter_errors f e in
    match view self with
    | Const _ -> ()
    | Arrow (args, ret) ->
      List.iter recurse args;
      recurse ret
    | Error err -> f (self.loc, err)

  let error_set self : Error_set.t =
    object
      method iter_errors f = iter_errors f self
    end
end

(** An expression of the meta language.

    The meta language is a basic ML-like, with an imperative flavor,
    designed to produce proofs and expressions when executed.
    It has no logical meaning in itself.
*)
module Meta_expr = struct
  type ty = Meta_ty.t

  type var = ty Var.t

  type value =
    | V_int of int
    | V_string of string
    | V_bool of bool
    | V_unit

  let pp_value out = function
    | V_int i -> Fmt.int out i
    | V_string s -> Fmt.string_quoted out s
    | V_bool b -> Fmt.bool out b
    | V_unit -> Fmt.string out "()"

  (* TODO: list comprehensions *)

  type t = view with_loc
  (** An expression *)

  and view =
    | Value of value
    | Var of var
    | Binop of Const.t * t * t
    | App of t * t list
    | Expr_lit of Expr.t  (** between '$' *)
    | List_lit of t list
    | Record of {
        fields: (Const.t * t) list;
        extends: t option;
      }
    | Fun of var list * block_expr
    | If of t * t * t option
    | Cond of {
        cases: (t * t) list;
        default: t;
      }
    | Match of {
        lhs: t;
        cases: match_case list;
        default: t option;
      }
    | Block_expr of block_expr
    | Error of Error.t
    (* TODO: remove, replace with primitive? *)
    | Const_accessor of Const.t * accessor

  and match_case = {
    pat: pattern;
    guard: t option;
    rhs: t;
  }

  and pattern = pattern_view with_loc

  and pattern_view =
    | P_any
    | P_var of var
    | P_cstor of {
        c: string;
        args: pattern list;
      }
    | P_record of {
        fields: string * pattern list;
        rest: bool;  (** ".." field to ignore the rest? *)
      }

  and accessor = Const.t
  (** Label to access a property of some logical constant. *)

  and binding = var * t

  and block_expr = { stmts: block_stmt list } [@@unboxed]
  (** A block expression, made of statements, but returning a value. *)

  and block_stmt = block_stmt_view with_loc
  (** A single statement in a block.

      Think of [let x = 1; ] in rust, or [foo()] in [foo(); bar();] in OCaml *)

  and block_stmt_view =
    | Blk_let of binding
    | Blk_eval of t (* x *)
    | Blk_return of t (* return from function *)
    | Blk_error of Error.t
  (* TODO: Blk_var of binding? *)
  (* TODO: Blk_set of binding? *)
  (* TODO: Blk_while of t * block_stmt list ? *)

  let mk_bl ~loc view : block_stmt = { loc; view }

  let pp_accessor : accessor Fmt.printer = Const.pp

  let rec pp_rec out (self : t) : unit =
    match self.view with
    | Value v -> pp_value out v
    | Const_accessor (c, acc) ->
      (* FIXME
         Fmt.fprintf out "%a'%a" Const.pp c pp_accessor acc *)
      assert false
    | Var v -> Var.pp out v
    | App (f, []) -> pp_rec out f
    | App (f, args) ->
      Fmt.fprintf out "(@[<hv>%a@ %a@])" pp_rec f (pp_list pp_rec) args
    | Binop (op, a, b) ->
      (* TODO: use some infix notation? {x op y}? instead of do blocks *)
      Fmt.fprintf out "(@[%a@ %a@ %a@])" Const.pp op pp_rec a pp_rec b
    | List_lit l -> Fmt.fprintf out "[@[%a@]]" (pp_list ~sep:", " pp_rec) l
    | Expr_lit e ->
      (* TODO: take a notation to print properly, binders included *)
      Expr.pp_sexp out e
    | Record { fields; extends } ->
      (* FIXME: think of a syntax for that *)
      let pp_rest out =
        match extends with
        | None -> ()
        | Some e -> Fmt.fprintf out ",@ .. %a" pp_rec e
      and pp_pair out (f, e) =
        Fmt.fprintf out "@[<2>%a:@ %a@]" Const.pp f pp_rec e
      in
      Fmt.fprintf out "{@[%a%t@]}" (pp_list ~sep:", " pp_pair) fields pp_rest
    | Fun (vars, blk) ->
      Fmt.fprintf out "(@[<hv>fn (@[%a@])@ %a@])" (pp_list pp_var_ty) vars
        pp_block_stmts blk.stmts
    | Error e -> Fmt.fprintf out "<@[error %a@]>" Error.pp e
    | If (a, b, None) -> Fmt.fprintf out "(@[if %a@ %a@])" pp_rec a pp_rec b
    | If (a, b, Some c) ->
      Fmt.fprintf out "(@[if %a@ %a@ %a@])" pp_rec a pp_rec b pp_rec c
    | Cond { cases; default } ->
      let ppcase out (c, e) = Fmt.fprintf out "(@[%a@ %a@])" pp_rec c pp_rec e
      and ppdefault out d = Fmt.fprintf out "(@[default@ %a@])" pp_rec d in
      Fmt.fprintf out "(@[cond@ %a@ %a@])" (pp_list ppcase) cases ppdefault
        default
    | Match _ -> assert false (* TODO *)
    | Block_expr e ->
      Fmt.fprintf out "@[<hv0>{@;<0 1>@[<v>%a@]@,}@]" pp_block_expr e

  and pp_var_ty out v = Var.pp_with_ty Meta_ty.pp out v

  and pp_block_expr out (b : block_expr) : unit =
    let { stmts } = b in
    pp_block_stmts out stmts

  and pp_block_stmts out l =
    List.iteri
      (fun i e ->
        if i > 0 then Fmt.fprintf out "@,";
        pp_block_stmt out e)
      l

  and pp_block_stmt out (st : block_stmt) : unit =
    match st.view with
    | Blk_let (v, e) -> Fmt.fprintf out "(@[<2>let %a %a@])" Var.pp v pp_rec e
    | Blk_eval e -> pp_rec out e
    | Blk_return e -> Fmt.fprintf out "(@[return %a@])" pp_rec e
    | Blk_error err -> Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  let pp out e = Fmt.fprintf out "@[%a@]" pp_rec e

  let mk ~loc view : t = { view; loc }

  let expr_lit ~loc e : t = mk ~loc (Expr_lit e)

  let apply f args : t =
    match args with
    | [] -> f
    | _ ->
      let loc = List.fold_left (fun l e -> Loc.Infix.(l ++ e.loc)) f.loc args in
      mk ~loc (App (f, args))

  let[@inline] view (e : t) = e.view

  let[@inline] loc (e : t) = e.loc

  let rec iter_errors f (e : t) =
    let recurse e = iter_errors f e in
    let recurse2 (a, b) =
      recurse a;
      recurse b
    in
    let recurse_ty = Meta_ty.iter_errors f in
    let recurse_v v = Option.iter recurse_ty v.Var.ty in
    match view e with
    | Value _ -> ()
    | Var v -> recurse_v v
    | Binop (_, a, b) ->
      recurse a;
      recurse b
    | App (f, args) ->
      recurse f;
      List.iter recurse args
    | Expr_lit e -> Expr.iter_errors f e
    | List_lit l -> List.iter recurse l
    | Fun (vs, bod) ->
      List.iter recurse_v vs;
      iter_block_errors f bod
    | If (a, b, c) ->
      recurse a;
      recurse b;
      Option.iter recurse c
    | Cond { cases; default } ->
      List.iter recurse2 cases;
      recurse default
    | Error err -> f (e.loc, err)
    | Block_expr bl -> iter_block_errors f bl
    | Match _ -> assert false (* FIXME *)
    | Record _ -> assert false (* FIXME *)
    | Const_accessor _ -> assert false (* FIXME *)

  and iter_block_stmt f (stmt : block_stmt) =
    match stmt.view with
    | Blk_return e | Blk_eval e -> iter_errors f e
    | Blk_error err -> f (stmt.loc, err)
    | Blk_let (x, e) ->
      Option.iter (Meta_ty.iter_errors f) x.Var.ty;
      iter_errors f e

  and iter_block_errors f (bl : block_expr) : unit =
    List.iter (iter_block_stmt f) bl.stmts

  let error_set (e : t) : Error_set.t =
    object
      method iter_errors f = iter_errors f e
    end
end

(** Structured proofs.

    We draw some inspiration from Lamport's
    "how to write a 21st century proof". *)
module Proof = struct
  (** A local goal in a proof *)

  type proof_var = Const.t
  (** A variable refering to the theorem obtained from another proof,
      or from earlier in the same proof. *)

  type t = view with_loc
  (** A (structured) proof. *)

  and view =
    | Exact of Meta_expr.t  (** A meta-expression returning the theorem. *)
    | By of {
        thm_args: proof_var list;
        solver: Meta_expr.t;
      }
        (** Call a solver on the goal, with the list of given theorems
                as first parameter. *)
    | Structured of {
        goal: Goal.t;  (** The initial goal to prove. *)
        block: block;
      }  (** Structured proof, with intermediate steps. *)
    | Error of Error.t  (** Parsing error *)

  and block = {
    steps: block_elt list;  (** Intermediate steps in the proof. *)
    qed: t;
        (** The justification for the last required goal, expected to
        use results from {!steps}.

        The sequent this must prove is the one from
        the latest "SS_suffices" in {!steps}, or, if no such step
        exists, the initial goal.
    *)
  }
  (** Structured proof *)

  and block_elt = block_elt_view with_loc
  (** A step in a composite proof. *)

  and block_elt_view =
    | Block_suffices of {
        goal: Goal.t;
        new_implies_old: block;
      }  (** new goal, with proof that it implies current goal. *)
    | Block_have of {
        name: Const.t;
        goal: Goal.t;
        proof: block;
      }  (** prove a lemma, to be used later. This binds [name]. *)
    | Block_let of {
        var: Meta_expr.var;
        rhs: Meta_expr.t;
      }  (** Define a meta-expression. This binds [var]. *)
    | Block_pick of {
        x: Expr.var;
        cond: Expr.t;
        proof: block;
      }
        (** Introduce a new variable using "select" and
            a proof of existence. *)
    (* TODO: case *)
    | Block_error of Error.t  (** Parse error in a statement *)

  let pp_proof_var out (v : proof_var) : unit = Const.pp out v

  let rec pp out (self : t) : unit =
    match self.view with
    | Exact e -> Fmt.fprintf out "(@[exact@ %a@])" Meta_expr.pp e
    | By { solver; thm_args } ->
      let pp_arg out a = Fmt.fprintf out ",@ %a" pp_proof_var a in
      Fmt.fprintf out "(@[<2>by %a" Meta_expr.pp solver;
      List.iter (pp_arg out) thm_args;
      Fmt.fprintf out "@])"
    | Structured { goal; block } ->
      Fmt.fprintf out "(@[<v>";
      Fmt.fprintf out "(@[prove %a@])@ " Goal.pp goal;
      pp_block out block;
      Fmt.fprintf out "@])"
    | Error err -> Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  and pp_block out { steps; qed } =
    let pp_step s = Fmt.fprintf out "@[%a@]@," pp_block_elt s in
    Fmt.fprintf out "@[<hv>";
    List.iter pp_step steps;
    pp out qed;
    Fmt.fprintf out "@]"

  and pp_block_elt out (self : block_elt) : unit =
    match self.view with
    | Block_suffices { goal; new_implies_old } ->
      Fmt.fprintf out "(@[@[<2>suffices %a {@ %a@]@ }@])" Goal.pp goal pp_block
        new_implies_old
    | Block_have { name; goal; proof } ->
      Fmt.fprintf out "(@[@[<2>have %a@ %a@ {@ %a@]@ }@])" Const.pp name Goal.pp
        goal pp_block proof
    | Block_let { var; rhs } ->
      Fmt.fprintf out "(@[@[<2>let %a@ %a@])" Var.pp var Meta_expr.pp rhs
    | Block_pick { x; cond; proof } ->
      Fmt.fprintf out "(@[@[<2>pick %a@ %a@ {@ %a@]@ }@])" Var.pp x Expr.pp cond
        pp_block proof
    | Block_error err -> Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  let[@inline] mk ~loc view : t = { loc; view }

  let[@inline] view (self : t) = self.view

  let[@inline] loc (self : t) = self.loc

  let exact ~loc e : t = mk ~loc (Exact e)

  let by ~loc solver thm_args : t = mk ~loc (By { solver; thm_args })

  let structured ~loc goal block : t = mk ~loc (Structured { goal; block })

  let error ~loc e : t = mk ~loc (Error e)

  let mk_bl ~loc view : block_elt = { loc; view }

  let bl_error ~loc e : block_elt = mk_bl ~loc @@ Block_error e

  let bl_suffices ~loc goal proof : block_elt =
    mk_bl ~loc @@ Block_suffices { goal; new_implies_old = proof }

  let bl_have ~loc name goal proof : block_elt =
    mk_bl ~loc @@ Block_have { name; goal; proof }

  let bl_let ~loc var rhs : block_elt = mk_bl ~loc @@ Block_let { var; rhs }

  let bl_pick ~loc x cond proof : block_elt =
    mk_bl ~loc @@ Block_pick { x; cond; proof }

  let rec iter_errors f (self : t) =
    let recurse_e = Meta_expr.iter_errors f in
    match view self with
    | Exact e -> recurse_e e
    | By { thm_args = _; solver } -> recurse_e solver
    | Structured { goal; block } ->
      Goal.iter_errors f goal;
      iter_errors_block f block
    | Error err -> f (self.loc, err)

  and iter_errors_block f (bl : block) =
    List.iter (iter_errors_block_elt f) bl.steps;
    iter_errors f bl.qed

  and iter_errors_block_elt f (ble : block_elt) =
    let recurse_e = Expr.iter_errors f in
    let recurse_me = Meta_expr.iter_errors f in
    match ble.view with
    | Block_have { name = _; goal; proof } ->
      iter_errors_block f proof;
      Goal.iter_errors f goal
    | Block_pick { x; cond; proof } ->
      Option.iter recurse_e x.Var.ty;
      recurse_e cond;
      iter_errors_block f proof
    | Block_let { var; rhs } ->
      Option.iter (Meta_ty.iter_errors f) var.Var.ty;
      recurse_me rhs
    | Block_suffices { goal; new_implies_old } ->
      Goal.iter_errors f goal;
      iter_errors_block f new_implies_old
    | Block_error err -> f (ble.loc, err)

  let error_set e : Error_set.t =
    object
      method iter_errors f = iter_errors f e
    end
end

(** Toplevel statements *)
module Top = struct
  type t = view with_loc

  and view =
    | Enter_file of string
    | Def of {
        name: Const.t;
        vars: Expr.var list;
        ret: Expr.ty option;
        body: Expr.t;
      }
    | Decl of {
        name: Const.t;
        ty: Expr.ty;
      }
    | Fixity of {
        name: Const.t;
        fixity: fixity;
      }
    | Axiom of {
        name: Const.t;
        thm: Expr.t;
      }
    | Goal of {
        goal: Goal.t;
        proof: Proof.block;
      }  (** Anonymous goal + proof *)
    | Theorem of {
        name: Const.t;
        goal: Goal.t;
        proof: Proof.block;
      }  (** Theorem + proof *)
    | Show of Expr.t
    | Eval of Meta_expr.t
    | Error of Error.t  (** Parse error *)

  (* TODO  | Top_def_ty of string *)
  (* TODO: | Top_def_proof_rule *)
  (* TODO: | Top_def_rule *)
  (* TODO: | Top_def_tactic *)

  let[@inline] view st = st.view

  let[@inline] loc st = st.loc

  let pp out (self : t) : unit =
    let pp_ty_opt out ty =
      match ty with
      | None -> Fmt.string out "_"
      | Some ty -> Expr.pp out ty
    in
    match self.view with
    | Enter_file f -> Fmt.fprintf out "(@[enter_file %S@])" f
    | Def { name; vars = []; ret; body } ->
      Fmt.fprintf out "(@[<1>def %a ()@ %a@ %a@])" Const.pp name pp_ty_opt ret
        Expr.pp body
    | Def { name; vars; ret; body } ->
      Fmt.fprintf out "(@[<1>def %a (@[%a@]) %a@ %a@])" Const.pp name
        (pp_list Expr.pp_var_ty) vars pp_ty_opt ret Expr.pp body
    | Decl { name; ty } ->
      Fmt.fprintf out "(@[<1>decl %a@ %a@])" Const.pp name Expr.pp ty
    | Fixity { name; fixity } ->
      Fmt.fprintf out "(@[<1>fixity %a %a@])" Const.pp name Fixity.pp_syntax
        fixity
    | Axiom { name; thm } ->
      Fmt.fprintf out "(@[<1>axiom %a@ %a@])" Const.pp name Expr.pp thm
    | Goal { goal; proof } ->
      Fmt.fprintf out "(@[@[<hv1>goal %a {@ %a@]@ }@])" Goal.pp goal
        Proof.pp_block proof
    | Theorem { name; goal; proof } ->
      Fmt.fprintf out "(@[<hv>@[<2>theorem %a@ %a {@ %a@]@ }@])" Const.pp name
        Goal.pp goal Proof.pp_block proof
    | Show e -> Fmt.fprintf out "(@[<1>show@ %a@])" Expr.pp e
    | Eval e -> Fmt.fprintf out "(@[<1>eval@ %a@])" Meta_expr.pp e
    | Error e -> Fmt.fprintf out "(@[<hov1>error@ @[%a@]@])" Error.pp e

  let to_string = Fmt.to_string pp

  let pp_quoted = Fmt.within "`" "`" pp

  let make ~loc view : t = { loc; view }

  let enter_file ~loc f : t = make ~loc (Enter_file f)

  let def ~loc name vars ret body : t =
    make ~loc (Def { name; ret; vars; body })

  let decl ~loc name ty : t = make ~loc (Decl { name; ty })

  let fixity ~loc name f : t = make ~loc (Fixity { name; fixity = f })

  let axiom ~loc name e : t = make ~loc (Axiom { name; thm = e })

  let goal ~loc goal proof : t = make ~loc (Goal { goal; proof })

  let theorem ~loc name g p : t =
    make ~loc (Theorem { name; goal = g; proof = p })

  let show ~loc e : t = make ~loc (Show e)

  let eval ~loc e : t = make ~loc (Eval e)

  let error ~loc e : t = make ~loc (Error e)

  let iter_errors f (self : t) : unit =
    let recurse_e = Expr.iter_errors f in
    let recurse_v v = Option.iter recurse_e v.Var.ty in
    let recurse_prbl = Proof.iter_errors_block f in
    let recurse_goal = Goal.iter_errors f in
    match view self with
    | Enter_file _ -> ()
    | Def { name = _; vars; ret; body } ->
      List.iter recurse_v vars;
      Option.iter recurse_e ret;
      recurse_e body
    | Decl { name = _; ty } -> recurse_e ty
    | Fixity _ -> ()
    | Axiom { name = _; thm } -> recurse_e thm
    | Goal { goal; proof } | Theorem { name = _; goal; proof } ->
      recurse_goal goal;
      recurse_prbl proof
    | Show e -> recurse_e e
    | Eval e -> Meta_expr.iter_errors f e
    | Error err -> f (self.loc, err)

  let error_set self : Error_set.t =
    object
      method iter_errors f = iter_errors f self
    end

  let error_set_l (l : t list) : Error_set.t =
    CCSeq.of_list l |> CCSeq.map error_set |> Error_set.merge_seq
end
