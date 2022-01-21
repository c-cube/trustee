
open Common_

type fixity = Fixity.t

type 'a with_loc = {
  loc: Loc.t;
  view: 'a;
}

(** A constant, with location. *)
module Const = struct
  type t = Name.t with_loc
  let make ~loc (name:Name.t) : t = {view=name;loc}
  let make_str ~loc s = make ~loc (Name.make s)
  let pp out (self:t) = Name.pp out self.view
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

  let make ?(kind=V_normal) ~loc name ty : _ t =
    {name; ty; kind; loc=loc; }

  let pp out v = Fmt.string out v.name
  let to_string v = Fmt.to_string pp v
  let pp_with_ty ppty out self =
    match self.ty with
    | None -> Fmt.string out self.name
    | Some ty -> Fmt.fprintf out "(@[%s@ : %a@])" self.name ppty ty
end

(** A logical expression. *)
module Expr = struct
  type t = view with_loc
  and ty = t
  and var = ty Var.t
  and binding = var * t

  and view =
    | Type
    | Ty_arrow of ty * ty
    | Var of var
    | Const of Const.t
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

  let unfold_app e : t * t list =
    let rec aux acc e = match e.view with
      | App (f, a) -> aux (a @ acc) f
      | _ -> e, acc
    in aux [] e

  let rec pp_ (p:_) out (e:t) : unit =
    match e.view with
    | Type -> Fmt.string out "type"
    | Var v -> Var.pp out v
    | Ty_arrow (a,b) ->
      if p>1 then Fmt.char out '(';
      Fmt.fprintf out "%a@ -> %a" pp_atom_ a (pp_ p) b;
      if p>1 then Fmt.char out ')';
    | Const c -> Const.pp out c
    | App _ ->
      let f, args = unfold_app e in
      if p>0 then Fmt.char out '(';
      Fmt.fprintf out "@[%a@ %a@]" pp_atom_ f (pp_list pp_atom_) args;
      if p>0 then Fmt.char out ')';
    | Meta v -> Fmt.fprintf out "?%s" v.name
    | Lambda (vars,bod) ->
      if p>0 then Fmt.char out '(';
      Fmt.fprintf out "@[\\%a.@ %a@]" (pp_list pp_var_ty) vars (pp_ 0) bod;
      if p>0 then Fmt.char out ')';
    | Bind {b; vars; body; } ->
      if p>0 then Fmt.char out '(';
      Fmt.fprintf out "@[%a %a.@ %a@]"
        Const.pp b (pp_list pp_var_ty) vars (pp_ 0) body;
      if p>0 then Fmt.char out ')';
    | With (vars,bod) ->
      if p>0 then Fmt.char out '(';
      Fmt.fprintf out "@[with %a.@ %a@]" (pp_list pp_var_ty) vars (pp_ 0) bod;
      if p>0 then Fmt.char out ')';
    | Eq (a,b) ->
      (* TODO: actually, allow applications to be () free in there.
         we need proper precedences for that. *)
      if p>0 then Fmt.char out '(';
      Fmt.fprintf out "@[%a@ =@ %a@]" pp_atom_ a pp_atom_ b;
      if p>0 then Fmt.char out ')';
    | Wildcard -> Fmt.string out "_"
    | Let (bs,bod) ->
      if p>0 then Fmt.char out '(';
      let pp_b out (v,e) : unit =
        Fmt.fprintf out "@[%a@ := %a@]" Var.pp v (pp_ 0) e in
      Fmt.fprintf out "@[let %a in@ %a@]" (pp_list ~sep:" and " pp_b) bs (pp_ 0) bod;
      if p>0 then Fmt.char out ')';
  and pp_atom_ out e = pp_ max_int out e
  and pp_var_ty out v = Var.pp_with_ty (pp_ 0) out v

  let pp out e = Fmt.fprintf out "@[%a@]" (pp_ 0) e

  let mk_ ~loc view : t = {view; loc}

  let[@inline] view e = e.view
  let[@inline] loc e = e.loc
  let pp_quoted = Fmt.within "`" "`" @@ pp

  let type_ : t = mk_ ~loc:Loc.none Type
  let ty_var ~loc s : t = mk_ ~loc (Var (Var.make ~loc s (Some type_)))
  let ty_meta ~loc (s:string) : ty = mk_ ~loc (Meta {ty=Some type_; name=s})
  let ty_arrow ~loc a b : ty = mk_ ~loc (Ty_arrow (a,b))

  let var ~loc (v:var) : t = mk_ ~loc (Var v)
  let var' ~loc v ty : t = var ~loc (Var.make ~loc v ty)
  let const ~loc n : t = mk_ ~loc (Const n)
  let const_str ~loc n : t = const ~loc @@ Const.make_str ~loc n
  let meta ~loc (s:string) ty : t = mk_ ~loc (Meta {ty; name=s})
  let app (f:t) (args:t list) : t =
    if args=[] then f
    else mk_ ~loc:Loc.(union_l f.loc ~f:(fun e->e.loc) args) (App (f,args))
  let let_ ~loc bs bod : t = mk_ ~loc (Let (bs, bod))
  let with_ ~loc vs bod : t = mk_ ~loc (With (vs, bod))
  let lambda ~loc vs bod : t = mk_ ~loc (Lambda (vs, bod))
  let bind ~loc b vars body : t =
    mk_ ~loc (Bind {b; vars; body})
  let eq ~loc a b : t = mk_ ~loc (Eq (a,b))
  let wildcard ~loc () : t = mk_ ~loc Wildcard

  let to_string = Fmt.to_string @@ Fmt.hvbox pp
end

(** A logical substitution literal. *)
module Subst = struct
  type t = (string with_loc * Expr.t) list with_loc
  let mk_ ~loc view : t = {view; loc}
  let pp out s =
    let pppair out (v,e) = Fmt.fprintf out "(@[%s := %a@])" v.view Expr.pp e in
    Fmt.fprintf out "(@[%a@])" (pp_list ~sep:"," pppair) s.view
  let to_string = Fmt.to_string pp
end

(** A goal, ie. a sequent to prove. *)
module Goal = struct
  type t = {
    hyps: Expr.t list;
    concl: Expr.t;
    loc: Loc.t;
  }

  let make ~loc hyps concl : t = {hyps; concl;loc}
  let make_nohyps ~loc c : t = make ~loc [] c
  let loc self = self.loc

  let pp out (self:t) : unit =
    if CCList.is_empty self.hyps then (
      Fmt.fprintf out "@[<h>?- %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[<v>%a@ ?-@ %a@]"
        (pp_list Expr.pp) self.hyps Expr.pp self.concl
    )
  let to_string = Fmt.to_string pp
end

(** A type in the meta language. *)
module Meta_ty = struct
  type t = view with_loc
  and view =
    | Const of Const.t
    | Arrow of t list * t

  let mk ~loc view : t = {view;loc}
  let loc self = self.loc
  let view self = self.view

  let const c : t = mk ~loc:c.loc (Const c)
  let const_str ~loc s : t = const (Const.make_str loc s)
  let arrow args ret = match args with
    | [] -> ret
    | _ ->
      let loc = Loc.(union_l ret.loc ~f:loc args) in
      mk ~loc (Arrow (args, ret))
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

  (** An expression *)
  type t = view with_loc
  and view =
    | Value of value
    | Const of Name.t
    | Const_accessor of Const.t * accessor
    | Var of var
    | Binop of Const.t * t * t
    | App of t * t list
    | Expr_lit of Expr.t (** between '$' *)
    | Record of {
        fields: (Const.t * t) list;
        extends: t option;
      }
    | Fun of var list * block_expr
    | If of t * block_expr * block_expr
    | Match of {
        lhs: t;
        cases: match_case list;
        default: t option;
      }
    | Block_expr of block_expr

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
  and accessor = Name.t with_loc

  and binding = var * t

  (** A block expression, made of statements, but returning a value. *)
  and block_expr = {
    stmts: block_stmt list;
    ret: t
  }

  (** A single statement in a block.

      Think of [let x = 1; ] in rust, or [foo()] in [foo(); bar();] in OCaml *)
  and block_stmt = block_stmt_view with_loc
  and block_stmt_view =
    | Blk_let of binding
    | Blk_eval of t
    | Blk_return of t
    | Blk_if of {
        test: t;
        then_: block_stmt list;
        else_: block_stmt list option;
      }
    (* TODO: Blk_var of binding? *)
    (* TODO: Blk_set of binding? *)
    (* TODO: Blk_while of t * block_stmt list ? *)

  let pp_accessor : accessor Fmt.printer = fun out a -> Name.pp out a.view

  let rec pp_ p out (self:t) : unit =
    let pp' = pp_ p in
    match self.view with
    | Value v -> pp_value out v
    | Const c -> Name.pp out c
    | Const_accessor (c, acc) ->
      Fmt.fprintf out "%a'%a" Const.pp c pp_accessor acc
    | Var v -> Var.pp out v
    | App (f, []) -> pp' out f
    | App (f, args) ->
      wrap_ p 10 out @@ fun p ->
      Fmt.fprintf out "@[%a@ %a@]" pp0 f (pp_list (pp_ p)) args
    | Binop (op, a, b) ->
      wrap_ p 0 out @@ fun p ->
      Fmt.fprintf out "%a@ %a %a" (pp_ p) a Const.pp op (pp_ p) b
    | Expr_lit e ->
      Fmt.fprintf out "$ @[%a@] $" Expr.pp e
    | Record {fields; extends} ->
      let pp_rest out = match extends with
        | None -> ()
        | Some e -> Fmt.fprintf out ",@ .. %a" pp0 e
      and pp_pair out (f,e) =
        Fmt.fprintf out "@[<2>%a:@ %a@]" Const.pp f pp0 e
      in
      Fmt.fprintf out "{@[%a%t@]}"
        (pp_list ~sep:", " pp_pair) fields pp_rest
    | Fun (vars, blk) ->
      Fmt.fprintf out "@[<hv>@[<2>|%a| {@ %a@]@ }@]"
        (pp_list Var.pp) vars pp_block_expr blk

    | If (a, b, c) ->
      wrap_ p 5 out @@ fun _p ->
      Fmt.fprintf out "@[if %a@ { %a@ } else {@ %a@ }@]"
        pp0 a pp_block_expr b pp_block_expr c
    | Match _ -> assert false (* TODO *)
    | Block_expr e ->
      Fmt.fprintf out "@[<hv>{@[<1>@ %a@]@,}@]" pp_block_expr e

  and pp0 out e = pp_ 0 out e

  and pp_block_expr out (b:block_expr) : unit =
    let {stmts; ret} = b in
    Fmt.fprintf out "@[<v>";
    pp_block_stmts out stmts;
    pp0 out ret;
    Fmt.fprintf out "@]"

  and pp_block_stmts out l =
    List.iter (fun e -> Fmt.fprintf out "%a@, " pp_block_stmt e) l

  and pp_block_stmt out (st:block_stmt) : unit =
    match st.view with
    | Blk_let (v,e) ->
      Fmt.fprintf out "@[<2>let %a =@ %a@];" Var.pp v pp0 e
    | Blk_eval e -> Fmt.fprintf out "@[%a@];" pp0 e
    | Blk_return e -> Fmt.fprintf out "@[return %a@];" pp0 e
    | Blk_if {test; then_; else_} ->
      let ppelse out = match else_ with
        | None -> ()
        | Some bl -> Fmt.fprintf out " else {@ %a@]@ }" pp_block_stmts bl
      in
      Fmt.fprintf out "@[<hv>@[<2>if %a {@ %a@]@ @[<2>}%t@]@]"
        pp0 test pp_block_stmts then_ ppelse

  (* wrap in () if [p>p']; call [k (max p p')] to print the expr *)
  and wrap_ p p' out k =
    if p>=p' then (
      Fmt.fprintf out "(@[";
      k p;
      Fmt.fprintf out "@])";
    ) else k p'

  let pp = pp_ 0
end

(** Structured proofs.

    We draw some inspiration from Lamport's
    "how to write a 21st century proof". *)
module Proof = struct
  (** A local goal in a proof *)
  type sequent = sequent_view with_loc
  and sequent_view = {
    new_vars: Expr.var list;
    hyps: Expr.t list;
    goal: Expr.t
  }

  (** A variable refering to the theorem obtained from another proof,
      or from earlier in the same proof. *)
  type proof_var = Const.t

  (** A (structured) proof. *)
  type t = view with_loc
  and view = {
    goal: sequent;
    justification: justification;
  }
  and justification =
    | By of {
        thm_args: proof_var list;
        solver: Meta_expr.t;
      }
    (** Call a solver on the goal, with the list of given theorems
              as first parameter. *)

    | Structured of {
        steps: structured_step list;
        (** Intermediate steps in the proof. *)

        qed: justification;
        (** The justification for the last required goal, using {!steps}.
            The sequent this must prove is the one from
            the latest "SS_suffices" in {!steps}, or, if no such step
            exists, the goal of the initial proof.
        *)
      }
      (** Structured proof, with intermediate steps. *)

  (** A step in a composite proof. *)
  and structured_step = structured_step_view with_loc
  and structured_step_view =
    | SS_suffices of {
        goal: sequent;
        new_implies_old: justification;
      } (** new goal, with proof that it implies current goal *)
    | SS_have of {
        name: Const.t;
        goal: sequent;
        proof: justification;
      } (** prove a lemma, to be used later. This binds [name]. *)
    | SS_pick of {
        x: Expr.var;
        cond: Expr.t;
        proof: justification;
      } (** Introduce a new variable using "select" and
            a proof of existence. *)

  let pp_sequent out (s:sequent) =
    let pp_newvar out v =
      Fmt.fprintf out "@[new %a@],@," Expr.pp_var_ty v
    and pp_hyp out e =
      Fmt.fprintf out "@[assume %a@],@," Expr.pp e
    in
    let {new_vars; hyps; goal} = s.view in
    Fmt.fprintf out "@[<v>%a%aprove %a@]"
      (pp_list pp_newvar) new_vars
      (pp_list pp_hyp) hyps
      Expr.pp goal

  let pp_proof_var out (v:proof_var) : unit = Const.pp out v

  let rec pp out (self:t) : unit =
    let {goal; justification} = self.view in
    Fmt.fprintf out "@[<v>%a@ @[<2>proof:@ %a@]@]"
      pp_sequent goal pp_justification justification

  and pp_justification out = function
    | By {solver; thm_args} ->
      let pp_arg out a = Fmt.fprintf out ",@ %a" pp_proof_var a in
      Fmt.fprintf out "@[<2>by %a" Meta_expr.pp solver;
      List.iter (pp_arg out) thm_args;
      Fmt.fprintf out "@]"

    | Structured {steps; qed} ->
      let pp_step s = Fmt.fprintf out "- @[%a@]@," pp_structured_step s in
      Fmt.fprintf out "@[<v>";
      List.iter pp_step steps;
      pp_justification out qed;
      Fmt.fprintf out "@]"

  and pp_structured_step out (self:structured_step) : unit =
    match self.view with
    | SS_suffices {goal; new_implies_old} ->
      Fmt.fprintf out "@[suffices %a@ @[<2>proof:@ %a@]@]"
        pp_sequent goal pp_justification new_implies_old

    | SS_have {name; goal; proof} ->
      Fmt.fprintf out "@[@[<2>have %a := %a@]@ @[<2>proof:@ %a@]@]"
        Const.pp name pp_sequent goal pp_justification proof

    | SS_pick {x; cond; proof} ->
      Fmt.fprintf out "@[@[<2>pick %a where %a@]@ @[<2>proof:@ %a@]@]"
        Var.pp x Expr.pp cond pp_justification proof

end

(** Toplevel statements *)
module Top = struct
  type t = view with_loc
  and view =
    | Top_enter_file of string
    | Top_def of {
        name: Const.t;
        vars: Expr.var list;
        ret: Expr.ty option;
        body: Expr.t;
      }
    | Top_decl of {
        name: string with_loc;
        ty: Expr.ty;
      }
    | Top_fixity of {
        name: string with_loc;
        fixity: fixity;
      }
    | Top_axiom of {
        name: string with_loc;
        thm: Expr.t;
      }
    | Top_goal of {
        goal: Goal.t;
        proof: Proof.t;
      } (** Anonymous goal + proof *)
    | Top_theorem of {
        name: Const.t;
        goal: Goal.t;
        proof: Proof.t;
      } (** Theorem + proof *)
    | Top_show of Meta_expr.t
    | Top_error of Error.t (** Parse error *)

  (* TODO  | Top_def_ty of string *)
  (* TODO: | Top_def_proof_rule *)
  (* TODO: | Top_def_rule *)
  (* TODO: | Top_def_tactic *)

  let[@inline] view st = st.view
  let[@inline] loc st = st.loc
  let pp out (self:t) : unit =
    let pp_ty_opt out ty = match ty with
      | None -> ()
      | Some ty -> Fmt.fprintf out "@ : %a" Expr.pp ty
    in
    match self.view with
    | Top_enter_file f ->
      Fmt.fprintf out "@[enter_file '%s'@];" f
    | Top_def { name; vars=[]; ret; body } ->
      Fmt.fprintf out "@[<2>def %a%a :=@ %a@];"
        Const.pp name pp_ty_opt ret Expr.pp body
    | Top_def { name; vars; ret; body } ->
      Fmt.fprintf out "@[<hv2>@[<2>def %a %a%a :=@]@ %a@];"
        Const.pp name (pp_list Expr.pp_var_ty) vars
        pp_ty_opt ret Expr.pp body
    | Top_decl { name; ty } ->
      Fmt.fprintf out "@[<2>decl %s :@ %a@];"
        name.view Expr.pp ty
    | Top_fixity {name; fixity} ->
      Fmt.fprintf out "@[<2>fixity %s = %s@];"
        name.view (Fixity.to_string_syntax fixity)
    | Top_axiom { name; thm } ->
      Fmt.fprintf out "@[<hv>@[<2>axiom %s :=@ %a@];@]"
        name.view Expr.pp thm
    | Top_goal { goal; proof } ->
      Fmt.fprintf out "@[<hv>@[<2>goal %a@ proof %a@];@]"
        Goal.pp goal Proof.pp proof
    | Top_theorem { name; goal; proof } ->
      Fmt.fprintf out "@[<hv>@[<2>theorem %a :=@ %a@]@ @[<2>proof@ %a@]@];"
        Const.pp name Goal.pp goal Proof.pp proof
    | Top_show e -> Fmt.fprintf out "@[show %a@];" Meta_expr.pp e
    | Top_error e -> Fmt.fprintf out "<@[<hov2>error:@ @[%a@]@]>" Error.pp e

  let to_string = Fmt.to_string pp

  let make ~loc view : t = {loc; view}
  let enter_file ~loc f : t = make ~loc (Top_enter_file f)
  let def ~loc name vars ret body : t =
    make ~loc (Top_def {name; ret; vars; body})
  let decl ~loc name ty : t = make ~loc (Top_decl {name; ty})
  let fixity ~loc name f : t = make ~loc (Top_fixity {name; fixity=f})
  let axiom ~loc name e : t = make ~loc (Top_axiom {name; thm=e})
  let goal ~loc goal proof : t = make ~loc (Top_goal {goal; proof})
  let theorem ~loc name g p : t = make ~loc (Top_theorem{name; goal=g; proof=p})
  let show ~loc e : t = make ~loc (Top_show e)
  let error ~loc e : t = make ~loc (Top_error e)
end


