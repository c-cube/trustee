
open Sigs

module K = Kernel
module TyProof = Proof
module TyRule = TyProof.Rule

type location = Loc.t
type fixity = Fixity.t

type 'a with_loc = {
  loc: location;
  view: 'a;
}

type expr = view with_loc

and ty = expr

and var = {
  v_name: string;
  v_ty: ty option;
  v_kind: var_kind;
  v_loc: location;
}

and var_kind =
  | V_normal
  | V_at
  | V_question_mark

and binding = var * expr

and view =
  | Type
  | Ty_arrow of ty * ty
  | Var of var
  | K_const of K.const
  | K_expr of K.expr
  | Meta of {
      name: string;
      ty: ty option;
    }
  | Wildcard
  | App of expr * expr
  | Lambda of var list * expr
  | Bind of {
      b: expr;
      b_loc: location;
      vars: var list;
      body: expr;
    }
  | With of var list * expr
  | Eq of expr * expr
  | Let of binding list * expr

type subst = (string with_loc * expr) list with_loc

let noloc: location = Loc.none

let unfold_app e =
  let rec aux acc e = match e.view with
    | App (f, a) -> aux (a::acc) f
    | _ -> e, acc
  in aux [] e

let rec pp_ (p:_) out (e:expr) : unit =
  match e.view with
  | Type -> Fmt.string out "type"
  | Var v -> Fmt.string out v.v_name
  | Ty_arrow (a,b) ->
    if p>1 then Fmt.char out '(';
    Fmt.fprintf out "%a@ -> %a" pp_atom_ a (pp_ p) b;
    if p>1 then Fmt.char out ')';
  | K_const c -> K.Const.pp out c
  | K_expr e -> K.Expr.pp out e
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
  | Bind {b; vars; body; b_loc=_} ->
    if p>0 then Fmt.char out '(';
    Fmt.fprintf out "@[%a %a.@ %a@]"
      (pp_ p) b (pp_list pp_var_ty) vars (pp_ 0) body;
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
    let pp_b out (v,e) : unit = Fmt.fprintf out "@[%s@ := %a@]" v.v_name (pp_ 0) e in
    Fmt.fprintf out "@[let %a in@ %a@]" (pp_list ~sep:" and " pp_b) bs (pp_ 0) bod;
    if p>0 then Fmt.char out ')';
and pp_atom_ out e = pp_ max_int out e
and pp_var_ty out (v:var) : unit =
  match v.v_ty with
  | None -> Fmt.string out v.v_name
  | Some ty -> Fmt.fprintf out "(@[%s@ : %a@])" v.v_name (pp_ 0) ty

let pp out e = Fmt.fprintf out "@[%a@]" (pp_ 0) e

module Var = struct
  type t = var
  let make ?kind:(v_kind=V_normal) ~loc v_name v_ty : var =
    {v_name; v_ty; v_kind; v_loc=loc; }

  let pp out v = Fmt.string out v.v_name
  let to_string = Fmt.to_string pp
  let pp_with_ty = pp_var_ty
end

module Expr = struct
  type t = expr
  let mk_ ?(loc=noloc) view : t = {view; loc}

  let[@inline] view e = e.view
  let[@inline] loc e = e.loc
  let pp = pp
  let pp_quoted = Fmt.within "`" "`" @@ pp

  let type_ : t = mk_ Type
  let ty_var ~loc s : t = mk_ ~loc (Var (Var.make ~loc s (Some type_)))
  let ty_meta ~loc (s:string) : ty = mk_ ~loc (Meta {ty=Some type_; name=s})
  let ty_arrow ~loc a b : ty = mk_ ~loc (Ty_arrow (a,b))

  let var ~loc (v:var) : t = mk_ ~loc (Var v)
  let var' ~loc v ty : t = var ~loc (Var.make ~loc v ty)
  let of_k_expr ~loc e : t = mk_ ~loc (K_expr e)
  let of_k_const ~loc c : t = mk_ ~loc (K_const c)
  let meta ~loc (s:string) ty : t = mk_ ~loc (Meta {ty; name=s})
  let app (f:t) (a:t) : t = mk_ ~loc:Loc.(f.loc ++ a.loc) (App (f,a))
  let rec app_l f l = match l with [] -> f | x::xs -> app_l (app f x) xs
  let let_ ~loc bs bod : t = mk_ ~loc (Let (bs, bod))
  let with_ ~loc vs bod : t = mk_ ~loc (With (vs, bod))
  let lambda ~loc vs bod : t = mk_ ~loc (Lambda (vs, bod))
  let bind ~loc ~b_loc b vars body : t =
    mk_ ~loc (Bind {b; b_loc; vars; body})
  let eq ~loc a b : t =
    Log.debugf 6 (fun k->k"mk-eq loc=%a" Loc.pp loc);
    mk_ ~loc (Eq (a,b))
  let wildcard ~loc () : t = mk_ ~loc Wildcard

  let to_string = Fmt.to_string @@ Fmt.hvbox pp
end

module Subst = struct
  type t = subst
  let mk_ ?(loc=noloc) view : t = {view; loc}

  let pp out s =
    let pppair out (v,e) = Fmt.fprintf out "(@[%s := %a@])" v.view Expr.pp e in
    Fmt.fprintf out "(@[%a@])" (pp_list ~sep:"," pppair) s.view
  let to_string = Fmt.to_string pp
end

module Goal = struct
  type t = {
    hyps: Expr.t list;
    concl: Expr.t;
  }

  let make hyps concl = {hyps; concl}
  let make_nohyps c = make [] c

  let pp out (self:t) : unit =
    if CCList.is_empty self.hyps then (
      Fmt.fprintf out "@[<h>?- %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[<v>%a@ ?-@ %a@]"
        (pp_list Expr.pp) self.hyps Expr.pp self.concl
    )
  let to_string = Fmt.to_string pp
end

(** {2 Proofs} *)
module Proof = struct
  type t = top with_loc
  and top =
    | Proof_atom of step
    | Proof_steps of {
        lets: pr_let list;
        (** intermediate steps *)
        ret: step;
        (** proof to return *)
      }

  and pr_let =
    | Let_expr of string with_loc * expr
    | Let_step of string with_loc * step

  and step = step_view with_loc
  and step_view =
    | Pr_apply_rule of string with_loc * rule_arg list
    | Pr_sub_proof of t
    | Pr_error of unit Fmt.printer (* parse error *)

  (** An argument to a rule *)
  and rule_arg =
    | Arg_var of string with_loc
    | Arg_step of step
    | Arg_expr of expr
    | Arg_subst of subst

  type rule_signature = TyRule.signature

  let rec pp out (self:t) : unit =
    Fmt.fprintf out "@[<hv>@[<hv2>proof@ ";
    begin match self.view with
      | Proof_atom s -> pp_step ~top:true out s
      | Proof_steps {lets; ret} ->
        List.iter (fun l -> Fmt.fprintf out "%a@ " pp_pr_let l) lets;
        pp_step ~top:true out ret
    end;
    Fmt.fprintf out "@]@ end@]"

  and pp_pr_let out l =
    match l with
    | Let_expr (s,e) ->
      Fmt.fprintf out "@[<2>let expr %s =@ %a in@]" s.view Expr.pp e
    | Let_step (s,p) ->
      Fmt.fprintf out "@[<2>let %s =@ %a in@]"
        s.view (pp_step ~top:true) p

  and pp_step ~top out (s:step) : unit =
    match s.view with
    | Pr_apply_rule (r, []) when top -> Fmt.string out r.view
    | Pr_apply_rule (r, args) ->
      if not top then Fmt.char out '(';
      Fmt.fprintf out "@[<hv2>%s@ %a@]" r.view (pp_list pp_rule_arg) args;
      if not top then Fmt.char out ')';
    | Pr_sub_proof p -> pp out p
    | Pr_error e -> Fmt.fprintf out "<@[error:@ %a@]>" e ()

  and pp_rule_arg out (a:rule_arg) : unit =
    match a with
    | Arg_var s -> Fmt.string out s.view
    | Arg_step s -> pp_step ~top:false out s (* always in ( ) *)
    | Arg_expr e -> Expr.pp out e
    | Arg_subst s -> Subst.pp out s

  let pp_rule_signature = TyRule.pp_signature
  let to_string = Fmt.to_string pp

  let view p = p.view
  let loc p = p.loc
  let s_view s = s.view
  let s_loc s = s.loc

  let make ~loc lets ret = match lets with
    | [] -> {loc; view=Proof_atom ret}
    | _ -> {loc; view=Proof_steps {lets; ret}}

  let let_expr s e = Let_expr (s,e)
  let let_step s p = Let_step (s,p)

  let step_apply_rule ~loc r args : step = {loc; view=Pr_apply_rule (r, args)}
  let step_subproof ~loc p : step =
    match p.view with
    | Proof_atom s -> s (* inline sub-proof *)
    | _ -> {loc; view=Pr_sub_proof p}
  let step_error ~loc e : step = {loc; view=Pr_error e}

  let arg_var v = Arg_var v
  let arg_step v = Arg_step v
  let arg_expr v = Arg_expr v
  let arg_subst v = Arg_subst v
end

(** {2 Statements} *)

type top_statement = top_statement_view with_loc
and top_statement_view =
  | Top_enter_file of string
  | Top_def of {
      name: string with_loc;
      th_name: string with_loc option;
      vars: var list;
      ret: ty option;
      body: expr;
    }
  | Top_decl of {
      name: string with_loc;
      ty: ty;
    }
  | Top_fixity of {
      name: string with_loc;
      fixity: fixity;
    }
  | Top_axiom of {
      name: string with_loc;
      thm: expr;
    }
  | Top_goal of {
      goal: Goal.t;
      proof: Proof.t;
      (* TODO: instead, Meta_expr.toplevel_proof; *)
    }
  | Top_theorem of {
      name: string with_loc;
      goal: Goal.t;
      proof: Proof.t;
      (* TODO: instead, Meta_expr.toplevel_proof; *)
    }
  | Top_show of string with_loc
  | Top_show_expr of expr
  | Top_show_proof of Proof.t
  | Top_error of {
      msg: unit Fmt.printer; (* parse error *)
    }
  (* TODO  | Top_def_ty of string *)
  (* TODO: | Top_def_proof_rule *)
  (* TODO: | Top_def_rule *)
  (* TODO: | Top_def_tactic *)

module Top_stmt = struct
  type t = top_statement

  let[@inline] view st = st.view
  let[@inline] loc st = st.loc
  let pp out (self:t) : unit =
    let pp_ty_opt out ty = match ty with
      | None -> ()
      | Some ty -> Fmt.fprintf out "@ : %a" Expr.pp ty
    in
    let pp_th_name out th = match th with
      | None -> ()
      | Some th -> Fmt.fprintf out "@ by %s" th.view
    in
    match self.view with
    | Top_enter_file f ->
      Fmt.fprintf out "@[enter_file '%s' end@]" f
    | Top_def { name; th_name; vars=[]; ret; body } ->
      Fmt.fprintf out "@[<hv>@[<2>def %s%a%a :=@ %a@]@ end@]"
        name.view pp_ty_opt ret pp_th_name th_name pp body
    | Top_def { name; th_name; vars; ret; body } ->
      Fmt.fprintf out "@[<v>@[<v2>@[<2>def %s %a%a%a :=@]@ %a@]@ end@]"
        name.view (pp_list pp_var_ty) vars pp_ty_opt ret pp_th_name th_name pp body
    | Top_decl { name; ty } ->
      Fmt.fprintf out "@[<hv>@[<2>decl %s :@ %a@]@ end@]"
        name.view pp ty
    | Top_fixity {name; fixity} ->
      Fmt.fprintf out "@[<hv>@[<2>fixity %s = %s@]@ end@]"
        name.view (Fixity.to_string_syntax fixity)
    | Top_axiom { name; thm } ->
      Fmt.fprintf out "@[<hv>@[<2>axiom %s :=@ %a@]@ end@]"
        name.view pp thm
    | Top_goal { goal; proof } ->
      Fmt.fprintf out "@[<hv>@[<2>goal %a@ by %a@]@ end@]"
        Goal.pp goal Proof.pp proof
    | Top_theorem { name; goal; proof } ->
      Fmt.fprintf out "@[<hv>@[<2>theorem %s :=@ %a@]@ @[<2>by@ %a@]@ end@]"
        name.view Goal.pp goal Proof.pp proof
    | Top_show s -> Fmt.fprintf out "@[show %s end@]" s.view
    | Top_show_expr e -> Fmt.fprintf out "@[@[<hv2>show expr@ %a@]@ end@]" Expr.pp e
    | Top_show_proof p -> Fmt.fprintf out "@[show %a end@]" Proof.pp p
    | Top_error {msg} -> Fmt.fprintf out "<@[<hov2>error:@ @[%a@]@]>" msg ()

  let to_string = Fmt.to_string pp

  let make ~loc view : t = {loc; view}
  let enter_file ~loc f : t = make ~loc (Top_enter_file f)
  let def ~loc name ~th_name vars ret body : t =
    make ~loc (Top_def {name; th_name; ret; vars; body})
  let decl ~loc name ty : t = make ~loc (Top_decl {name; ty})
  let fixity ~loc name f : t = make ~loc (Top_fixity {name; fixity=f})
  let axiom ~loc name e : t = make ~loc (Top_axiom {name; thm=e})
  let goal ~loc goal proof : t = make ~loc (Top_goal {goal; proof})
  let theorem ~loc name g p : t = make ~loc (Top_theorem{name; goal=g; proof=p})
  let show ~loc s : t = make ~loc (Top_show s)
  let show_expr ~loc e : t = make ~loc (Top_show_expr e)
  let show_proof ~loc p : t = make ~loc (Top_show_proof p)
  let error ~loc e : t = make ~loc (Top_error {msg=e})
end

module Env = struct
  type t = {
    fixity: (string -> fixity);
    mutable rules: Proof.rule_signature Str_map.t;
    bool: expr;
    eq: expr;
    type_: expr;
  }

  let create ?(fixity=fun _ -> Fixity.normal) () : t =
    let type_ = Expr.var' ~loc:Loc.none "type" None in
    let self = {
      fixity;
      rules=Str_map.empty;
      type_;
      eq=Expr.var' ~loc:Loc.none "eq" None;
      bool=Expr.var' ~loc:Loc.none "bool" (Some type_)
    } in
    self

  let copy e : t = e
  let bool self = self.bool
  let eq self = self.eq
  let type_ self = self.type_

  let fixity self s = self.fixity s

  let declare_rule self s r =
    self.rules <- Str_map.add s r self.rules

  let find_rule self s : _ option =
    match TyRule.find_builtin s with
    | Some r -> Some (TyRule.signature r)
    | None -> Str_map.get s self.rules
end

