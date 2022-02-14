
(** Typed AST.

    This is the main AST representation that we use in the LSP
    and to manipulate the syntactic form of logic.

    Heavier lifting and actual proof checking are done with the
    {!Trustee_core.Kernel} expressions. However, these don't have any
    syntactic sugar nor locations so they are not well suited to
    user-facing processing.
*)

open Common_

module A = Parse_ast
module AE = A.Expr

type fixity = Fixity.t

type 'a with_loc = 'a With_loc.t = {
  loc: Loc.t;
  view: 'a;
}

(**/**)
(* module used for forward declarations *)
module Init_ = struct
  (** Bound variable *)
  type 'ty bvar = {
    id: ID.t;
    ty: 'ty;
    loc: Loc.t;
  }

  (** A meta-variable.

      These variables are used for type inference. They're to be bound
      to an actual type as type inference progresses. *)
  type 'ty meta_var = {
    id: ID.t;
    ty: 'ty;
    loc: Loc.t;
    mutable deref: 'ty option;
  }

  (** Logical expressions. *)
  type expr = {
    view: expr_view;
    ty: ty option;
    loc: Loc.t;
  }

  (** Types are represented with expressions. *)
  and ty = expr

  and expr_view =
    | Kind
    | Type
    | Ty_arrow of ty * ty
    | Var of var
    | BVar of ty bvar
    | Meta of ty meta_var
    | Const of {
        c: const;
        args: ty list;
      }
    | App of expr * expr
    | Lambda of ty bvar * expr
    | Eq of expr * expr
    | Let of binding list * expr
    | Error of Error.t

  (** Free variable *)
  and var = {
    name: string;
    ty: ty;
    loc: Loc.t;
  }

  (** Logical constant *)
  and const = {
    name: Name.t;
    ty: ty;
    loc: Loc.t;
    args: const_args;
  }

  and const_args =
    | C_arity of int
    | C_vars of ty bvar list

  and binding = ty bvar * expr

  let kind : expr = {view=Kind; ty=None; loc=Loc.none}
  let type_ : expr = {view=Type; loc=Loc.none; ty=Some kind}
end
(**/**)

(** A logical constant, with location. *)
module Const = struct
  open Init_

  type args = Init_.const_args =
    | C_arity of int
    | C_vars of ty bvar list

  type t = Init_.const = {
    name: Name.t;
    ty: ty;
    loc: Loc.t;
    args: const_args;
  }

  let pp out (self:t) = Name.pp out self.name
  let to_string self = Name.to_string self.name
  let[@inline] equal (a:t) (b:t) = Name.equal a.name b.name
  let[@inline] name (self:t) : Name.t = self.name
  let[@inline] loc (self:t) = self.loc
  let[@inline] args (self:t) = self.args

  let make ~loc ~ty ~args name : t = {loc;ty;args;name}
  let make_str ~loc ~ty ~args s : t = make ~loc ~ty ~args (Name.make s)

  let bool : t = make_str ~loc:Loc.none "bool" ~ty:type_ ~args:(C_arity 0)
end

type const = Const.t

(** Free variables. *)
module Var = struct
  open Init_
  type t = var = {
    name: string;
    ty: ty;
    loc: Loc.t;
  }

  let make ~loc name ty : t =
    {name; ty; loc=loc; }

  let pp out v = Fmt.string out v.name
  let to_string v = Fmt.to_string pp v
  let pp_with_ty ppty out self =
    Fmt.fprintf out "[@[%s@ %a@]]" self.name ppty self.ty
end

(** Bound variables. *)
module BVar = struct
  open Init_
  type 'a t = 'a bvar
  let[@inline] id (self:_ t) = self.id
  let[@inline] ty (self:_ t) = self.ty
  let[@inline] make ~loc id ty : _ t = { id; ty; loc=loc; }
  let[@inline] compare (a: _ t) (b: _ t) = ID.compare a.id b.id
  let[@inline] map_ty ~f (self:_ t) = {self with ty=f self.ty}
  let pp out (self:_ t) = ID.pp out self.id
  let to_string (self:_ t) = ID.to_string self.id
  let pp_with_ty ppty out (self:_ t) : unit =
    Fmt.fprintf out "[@[%a@ %a@]]" ID.pp self.id ppty self.ty

  (** Obtain a queryable object. *)
  let as_queryable ~ty_as_q (self:_ t) = object
    inherit Queryable.t
    method loc = self.loc
    method pp out () =
      let self = map_ty self ~f:ty_as_q in
      Fmt.fprintf out "@[bound variable:@ %a@]"
        (pp_with_ty Queryable.pp) self
  end
end

(** Meta variables, for type inference. *)
module Meta_var = struct
  open Init_
  type 'a t = 'a meta_var = {
    id: ID.t;
    ty: 'a;
    loc: Loc.t;
    mutable deref: 'a option;
  }

  let make ~loc ~ty (id:ID.t) : _ t = {loc; ty; id; deref=None}

  let[@inline] equal (a:_ t) (b:_ t) = ID.equal a.id b.id
  let[@inline] loc (self:_ t) = self.loc
  let[@inline] ty (self:_ t) = self.ty
  let[@inline] id (self:_ t) = self.id

  let pp out (self:_ t) = Fmt.fprintf out "?%a" ID.pp self.id
  let pp_with_ty ppty out (self:_ t) =
    Fmt.fprintf out "[@[?%a %a@]]" ID.pp self.id ppty self.ty
end


(** Logical expressions. *)
module Expr = struct
  open Init_

  type view = expr_view =
    | Kind
    | Type
    | Ty_arrow of ty * ty
    | Var of var
    | BVar of ty bvar
    | Meta of ty meta_var
    | Const of {
        c: const;
        args: ty list;
      }
    | App of expr * expr
    | Lambda of ty bvar * expr
    | Eq of expr * expr
    | Let of binding list * expr
    | Error of Error.t

  type t = expr = {
    view: expr_view;
    ty: ty option;
    loc: Loc.t;
  }
  type ty = t
  type var = Var.t
  type nonrec bvar = ty bvar
  type binding = var * t

  let[@inline] view (self:t) = self.view
  let[@inline] loc (self:t) = self.loc

  let type_ = Init_.type_

  (** Type of this expression.
      Do {b not} call on [kind]. *)
  let[@inline] ty_exn e = match e.ty with
    | Some ty -> ty
    | None -> assert false

  (**/**)
  let mk_ ~loc ~ty view : t = {view; loc; ty=Some ty}
  (**/**)

  let[@inline] is_eq_to_type (self:t) = match view self with Type -> true | _ -> false
  let[@inline] is_a_type (self:t) = is_eq_to_type (ty_exn self)

  let rec unfold_arrow e = match view e with
    | Ty_arrow (a,b) ->
      let args, ret = unfold_arrow b in
      a::args, ret
    | _ -> [], e

  let rec unfold_lambda e = match view e with
    | Lambda (v,bod) ->
      let vars, bold = unfold_lambda bod in
      v::vars, bod
    | _ -> [], e

  let unfold_app e =
    let rec aux acc e = match view e with
      | App (f, arg) -> aux (arg::acc) f
      | _ -> e, acc
    in aux [] e

  let rec pp out (e:t) : unit =
    match e.view with
    | Kind -> Fmt.string out "kind"
    | Type -> Fmt.string out "type"
    | Var v -> Var.pp out v
    | BVar v -> BVar.pp out v
    | Const {c;args=[]} -> Const.pp out c
    | Const {c;args} ->
      Fmt.fprintf out "(@[%a@ %a@])" Const.pp c (pp_list pp) args
    | Ty_arrow _ ->
      let a, b = unfold_arrow e in
      Fmt.fprintf out "(@[->@ %a@ %a@])" (pp_list pp) a pp b
    | App _ ->
      let f, args = unfold_app e in
      Fmt.fprintf out "(@[%a@ %a@])" pp f (pp_list pp) args;
    | Lambda _ ->
      let vs, bod = unfold_lambda e in
      Fmt.fprintf out "(@[lambda (@[%a@])@ %a@])"
        (pp_list pp_bvar_ty) vs pp bod
    | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
    | Meta m -> Meta_var.pp out m
    | Let (bs,bod) ->
      Fmt.fprintf out "(@[let@ (@[%a@])@ %a@])"
        (pp_list pp_binding) bs pp bod
    | Error err ->
      Fmt.fprintf out "(@[error@ %a@])" Error.pp err
  and pp_binding out (x,e) = Fmt.fprintf out "[@[%a@ %a@]]" BVar.pp x pp e
  and pp_var_ty out v = Var.pp_with_ty pp out v
  and pp_bvar_ty out v = BVar.pp_with_ty pp out v

  let to_string = Fmt.to_string @@ Fmt.hvbox pp

  (* dereference meta-variables as much as possible. *)
  let[@inline][@unroll 2] rec deref_ (e:expr) : expr =
    match e.view with
    | Meta {deref=Some u; _} -> deref_ u
    | _ -> e

  (** Iterate on immediate subterms *)
  let iter ~f ~f_bind b_acc (e:expr) : unit =
    Option.iter (fun u -> f b_acc u) e.ty;
    match view e with
    | Kind | Type | Const {args=[];_} | Meta _
    | Var _ | BVar _ | Error _ -> ()
    | Const {args;_} -> List.iter (f b_acc) args
    | Ty_arrow (a, b) | Eq (a,b) | App (a,b) ->
      f b_acc a;
      f b_acc b
    | Lambda (v, bod) ->
      f b_acc v.ty;
      let b_acc = f_bind b_acc v in
      f b_acc bod
    | Let (bs, bod) ->
      let b_acc =
        List.fold_left
          (fun b_acc ((v:bvar),u) ->
             f b_acc v.ty;
             f b_acc u;
             f_bind b_acc v)
        b_acc bs
      in
      f b_acc bod
end

type expr = Expr.t
type ty = Expr.ty

(** A logical substitution literal. *)
module Subst = struct
  type t = (Expr.var * Expr.t) list with_loc
  let mk_ ~loc view : t = {view; loc}
  let pp out (s:t) =
    let pppair out (v,e) = Fmt.fprintf out "(@[%a %a@])" Var.pp v Expr.pp e in
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

  let mk ~loc view : t = {loc;view}
  let goal ~loc ?(new_vars=[]) ~hyps concl : t =
    mk ~loc @@ Goal {hyps; concl; new_vars}
  let goal_nohyps ~loc c : t = goal ~loc ~hyps:[] c
  let error ~loc err : t = mk ~loc @@ Error err
  let loc self = self.loc

  let pp out (self:t) =
    let pp_newvar out v =
      Fmt.fprintf out "(@[new@ %a@])@," Expr.pp_var_ty v
    and pp_hyp out e =
      Fmt.fprintf out "(@[assume@ %a@])@," Expr.pp e
    in
    match self.view with
    | Goal {new_vars=[]; hyps=[]; concl; } -> Expr.pp out concl
    | Goal {new_vars; hyps; concl; } ->
      Fmt.fprintf out "(@[<hv>goal@ %a%a(@[prove@ %a@])@])"
        (pp_list pp_newvar) new_vars
        (pp_list pp_hyp) hyps
        Expr.pp concl
    | Error e -> Fmt.fprintf out "<@[error@ %a@]>" Error.pp e

  let to_string = Fmt.to_string pp
end

(* TODO
(** A type in the meta language. *)
module Meta_ty = struct
  type t = view with_loc
  and view =
    | Const of Const.t
    | Arrow of t list * t
    | Error of Error.t

  let mk ~loc view : t = {view;loc}
  let loc self = self.loc
  let view self = self.view

  let rec pp out (self:t) = match self.view with
    | Const c -> Const.pp out c
    | Arrow (args, ret) ->
      Fmt.fprintf out "(@[->@ %a@ %a@])" (pp_list pp) args pp ret
    | Error err ->
      Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  let const c : t = mk ~loc:c.loc (Const c)
  let const_str ~loc s : t = const (Const.make_str ~loc s)
  let arrow args ret = match args with
    | [] -> ret
    | _ ->
      let loc = Loc.(union_l ret.loc ~f:loc args) in
      mk ~loc (Arrow (args, ret))
end
*)

(* TODO
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
  (** An expression *)
  type t = view with_loc
  and view =
    | Value of value

    | Var of var
    | Binop of Const.t * t * t
    | App of t * t list
    | Expr_lit of Expr.t (** between '$' *)
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
        c: Name.t;
        args: pattern list;
      }
    | P_record of {
        fields: (Name.t * pattern list);
        rest: bool; (** ".." field to ignore the rest? *)
      }

  (** Label to access a property of some logical constant. *)
  and accessor = Const.t

  and binding = var * t

  (** A block expression, made of statements, but returning a value. *)
  and block_expr = {
    stmts: block_stmt list;
  } [@@unboxed]

  (** A single statement in a block.

      Think of [let x = 1; ] in rust, or [foo()] in [foo(); bar();] in OCaml *)
  and block_stmt = block_stmt_view with_loc
  and block_stmt_view =
    | Blk_let of binding
    | Blk_eval of t (* x *)
    | Blk_return of t (* return from function *)
    | Blk_error of Error.t
    (* TODO: Blk_var of binding? *)
    (* TODO: Blk_set of binding? *)
    (* TODO: Blk_while of t * block_stmt list ? *)

  let mk_bl ~loc view : block_stmt = {loc; view}

  let pp_accessor : accessor Fmt.printer = Const.pp

  let rec pp_rec out (self:t) : unit =
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
    | List_lit l ->
      Fmt.fprintf out "[@[%a@]]" (pp_list ~sep:", " pp_rec ) l
    | Expr_lit e ->
      (* TODO: take a notation to print properly, binders included *)
      Expr.pp_sexp out e
    | Record {fields; extends} ->
      (* FIXME: think of a syntax for that *)
      let pp_rest out = match extends with
        | None -> ()
        | Some e -> Fmt.fprintf out ",@ .. %a" pp_rec e
      and pp_pair out (f,e) =
        Fmt.fprintf out "@[<2>%a:@ %a@]" Const.pp f pp_rec e
      in
      Fmt.fprintf out "{@[%a%t@]}"
        (pp_list ~sep:", " pp_pair) fields pp_rest
    | Fun (vars, blk) ->
      Fmt.fprintf out "(@[<hv>fn (@[%a@])@ %a@])"
        (pp_list pp_var_ty) vars pp_block_stmts blk.stmts
    | Error e -> Fmt.fprintf out "<@[error %a@]>" Error.pp e

    | If (a, b, None) ->
      Fmt.fprintf out "(@[if %a@ %a@])"
        pp_rec a pp_rec b
    | If (a, b, Some c) ->
      Fmt.fprintf out "(@[if %a@ %a@ %a@])"
        pp_rec a pp_rec b pp_rec c
    | Cond {cases; default} ->
      let ppcase out (c,e) =
        Fmt.fprintf out "(@[%a@ %a@])" pp_rec c pp_rec e
      and ppdefault out d =
        Fmt.fprintf out "(@[default@ %a@])" pp_rec d
      in
      Fmt.fprintf out "(@[cond@ %a@ %a@])" (pp_list ppcase) cases ppdefault default
    | Match _ -> assert false (* TODO *)
    | Block_expr e ->
      Fmt.fprintf out "@[<hv0>{@;<0 1>@[<v>%a@]@,}@]" pp_block_expr e

  and pp_var_ty out v = Var.pp_with_ty Meta_ty.pp out v

  and pp_block_expr out (b:block_expr) : unit =
    let {stmts} = b in
    pp_block_stmts out stmts

  and pp_block_stmts out l =
    List.iteri
      (fun i e ->
        if i>0 then Fmt.fprintf out "@,";
        pp_block_stmt out e)
      l

  and pp_block_stmt out (st:block_stmt) : unit =
    match st.view with
    | Blk_let (v,e) ->
      Fmt.fprintf out "(@[<2>let %a %a@])" Var.pp v pp_rec e
    | Blk_eval e -> pp_rec out e
    | Blk_return e -> Fmt.fprintf out "(@[return %a@])" pp_rec e
    | Blk_error err ->
      Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  let pp out e = Fmt.fprintf out "@[%a@]" pp_rec e

  let mk ~loc view : t = {view;loc}

  let expr_lit ~loc e : t = mk ~loc (Expr_lit e)
  let apply f args : t = match args with
    | [] -> f
    | _ ->
      let loc = List.fold_left (fun l e -> Loc.Infix.(l ++ e.loc)) f.loc args in
      mk ~loc (App (f, args))
end
*)

(* TODO
(** Structured proofs.

    We draw some inspiration from Lamport's
    "how to write a 21st century proof". *)
module Proof = struct
  (** A local goal in a proof *)

  (** A variable refering to the theorem obtained from another proof,
      or from earlier in the same proof. *)
  type proof_var = Const.t

  (** A (structured) proof. *)
  type t = view with_loc
  and view =
    | Exact of Meta_expr.t
      (** A meta-expression returning the theorem. *)

    | By of {
        thm_args: proof_var list;
        solver: Meta_expr.t;
      }
      (** Call a solver on the goal, with the list of given theorems
                as first parameter. *)

    | Structured of {
        goal: Goal.t;
        (** The initial goal to prove. *)

        block: block;
      }
    (** Structured proof, with intermediate steps. *)

    | Error of Error.t
      (** Parsing error *)

  (** Structured proof *)
  and block = {
    steps: block_elt list;
    (** Intermediate steps in the proof. *)

    qed: t;
    (** The justification for the last required goal, expected to
        use results from {!steps}.

        The sequent this must prove is the one from
        the latest "SS_suffices" in {!steps}, or, if no such step
        exists, the initial goal.
    *)
  }

  (** A step in a composite proof. *)
  and block_elt = block_elt_view with_loc
  and block_elt_view =
    | Block_suffices of {
        goal: Goal.t;
        new_implies_old: block;
      } (** new goal, with proof that it implies current goal. *)

    | Block_have of {
        name: Const.t;
        goal: Goal.t;
        proof: block;
      } (** prove a lemma, to be used later. This binds [name]. *)

    | Block_let of {
        var: Meta_expr.var;
        rhs: Meta_expr.t;
      } (** Define a meta-expression. This binds [var]. *)

    | Block_pick of {
        x: Expr.var;
        cond: Expr.t;
        proof: block;
      } (** Introduce a new variable using "select" and
            a proof of existence. *)

    (* TODO: case *)

    | Block_error of Error.t
    (** Parse error in a statement *)

  let pp_proof_var out (v:proof_var) : unit = Const.pp out v

  let rec pp out (self:t) : unit =
    match self.view with
    | Exact e ->
      Fmt.fprintf out "(@[exact@ %a@])" Meta_expr.pp e

    | By {solver; thm_args} ->
      let pp_arg out a = Fmt.fprintf out ",@ %a" pp_proof_var a in
      Fmt.fprintf out "(@[<2>by %a" Meta_expr.pp solver;
      List.iter (pp_arg out) thm_args;
      Fmt.fprintf out "@])"

    | Structured {goal; block} ->
      Fmt.fprintf out "(@[<v>";
      Fmt.fprintf out "(@[prove %a@])@ " Goal.pp goal;
      pp_block out block;
      Fmt.fprintf out "@])"

    | Error err ->
      Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  and pp_block out {steps; qed} =
    let pp_step s = Fmt.fprintf out "@[%a@]@," pp_block_elt s in
    Fmt.fprintf out "@[<hv>";
    List.iter pp_step steps;
    pp out qed;
    Fmt.fprintf out "@]"

  and pp_block_elt out (self:block_elt) : unit =
    match self.view with
    | Block_suffices {goal; new_implies_old} ->
      Fmt.fprintf out "(@[@[<2>suffices %a {@ %a@]@ }@])"
        Goal.pp goal pp_block new_implies_old

    | Block_have {name; goal; proof} ->
      Fmt.fprintf out "(@[@[<2>have %a@ %a@ {@ %a@]@ }@])"
        Const.pp name Goal.pp goal pp_block proof

    | Block_let {var; rhs} ->
      Fmt.fprintf out "(@[@[<2>let %a@ %a@])"
        Var.pp var Meta_expr.pp rhs

    | Block_pick {x; cond; proof} ->
      Fmt.fprintf out "(@[@[<2>pick %a@ %a@ {@ %a@]@ }@])"
        Var.pp x Expr.pp cond pp_block proof

    | Block_error err ->
      Fmt.fprintf out "(@[error@ %a@])" Error.pp err

  let mk ~loc view : t = {loc;view}

  let exact ~loc e : t = mk ~loc (Exact e)
  let by ~loc solver thm_args : t = mk ~loc (By { solver; thm_args })
  let structured ~loc goal block : t = mk ~loc (Structured {goal; block})
  let error ~loc e : t = mk ~loc (Error e)

  let mk_bl ~loc view : block_elt = {loc; view}
  let bl_error ~loc e : block_elt =
    mk_bl ~loc @@ Block_error e
  let bl_suffices ~loc goal proof : block_elt =
    mk_bl ~loc @@ Block_suffices {goal; new_implies_old=proof}
  let bl_have ~loc name goal proof : block_elt =
    mk_bl ~loc @@ Block_have {name; goal; proof}
  let bl_let ~loc var rhs : block_elt =
    mk_bl ~loc @@ Block_let {var; rhs}
  let bl_pick ~loc x cond proof : block_elt =
    mk_bl ~loc @@ Block_pick {x; cond; proof}
end
*)

(** Toplevel statements *)
module Top = struct
  type t = view with_loc
  and view =
    | Enter_file of string
    | Def of {
        name: Const.t;
        vars: Expr.var list;
        ret: Expr.ty;
        body: Expr.t;
      }
    | Decl of Const.t
    | Fixity of {
        name: Const.t;
        fixity: fixity;
      }
    | Axiom of {
        name: Const.t;
        thm: Expr.t;
      }
    | Show of Expr.t
    | Error of Error.t (** Parse error *)
   (*  TODO
    | Goal of {
        goal: Goal.t;
        proof: Proof.block;
      } (** Anonymous goal + proof *)
    | Theorem of {
        name: Const.t;
        goal: Goal.t;
        proof: Proof.block;
      } (** Theorem + proof *)
    | Eval of Meta_expr.t
       *)

  (* TODO  | Top_def_ty of string *)
  (* TODO: | Top_def_proof_rule *)
  (* TODO: | Top_def_rule *)
  (* TODO: | Top_def_tactic *)

  let[@inline] view st = st.view
  let[@inline] loc st = st.loc
  let pp out (self:t) : unit =
    match self.view with
    | Enter_file f ->
      Fmt.fprintf out "(@[enter_file %S@])" f
    | Def { name; vars=[]; ret; body } ->
      Fmt.fprintf out "(@[<1>def %a ()@ %a@ %a@])"
        Const.pp name Expr.pp ret Expr.pp body
    | Def { name; vars; ret; body } ->
      Fmt.fprintf out "(@[<1>def %a (@[%a@]) %a@ %a@])"
        Const.pp name (pp_list Expr.pp_var_ty) vars
        Expr.pp ret Expr.pp body
    | Decl { name; ty } ->
      Fmt.fprintf out "(@[<1>decl %a@ %a@])"
        Name.pp name Expr.pp ty
    | Fixity {name; fixity} ->
      Fmt.fprintf out "(@[<1>fixity %a %a@])"
        Const.pp name Fixity.pp_syntax fixity
    | Axiom { name; thm } ->
      Fmt.fprintf out "(@[<1>axiom %a@ %a@])"
        Const.pp name Expr.pp thm
    | Show e -> Fmt.fprintf out "(@[<1>show@ %a@])" Expr.pp e
    | Error e -> Fmt.fprintf out "(@[<hov1>error@ @[%a@]@])" Error.pp e
    (*
    | Goal { goal; proof } ->
      Fmt.fprintf out "(@[@[<hv1>goal %a {@ %a@]@ }@])"
        Goal.pp goal Proof.pp_block proof
    | Theorem { name; goal; proof } ->
      Fmt.fprintf out "(@[<hv>@[<2>theorem %a@ %a {@ %a@]@ }@])"
        Const.pp name Goal.pp goal Proof.pp_block proof
    | Eval e -> Fmt.fprintf out "(@[<1>eval@ %a@])" Meta_expr.pp e
    *)

  let to_string = Fmt.to_string pp
  let pp_quoted = Fmt.within "`" "`" pp

  let make ~loc view : t = {loc; view}
  let enter_file ~loc f : t = make ~loc (Enter_file f)
  let def ~loc name vars ret body : t =
    make ~loc (Def {name; ret; vars; body})
  let decl ~loc c : t = make ~loc (Decl c)
  let fixity ~loc name f : t = make ~loc (Fixity {name; fixity=f})
  let axiom ~loc name e : t = make ~loc (Axiom {name; thm=e})
  let show ~loc e : t = make ~loc (Show e)
  let error ~loc e : t = make ~loc (Error e)
      (* TODO
  let goal ~loc goal proof : t = make ~loc (Goal {goal; proof})
  let theorem ~loc name g p : t = make ~loc (Theorem{name; goal=g; proof=p})
  let eval ~loc e : t = make ~loc (Eval e)
         *)
end

