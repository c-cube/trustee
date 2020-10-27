
open Sigs

module K = Kernel

type position = Position.t

type 'a with_pos = {
  pos: position;
  view: 'a;
}

type expr = view with_pos

and ty = expr

and var = {
  v_name: string;
  v_ty: ty option;
  v_kind: var_kind
}

and var_kind =
  | V_normal
  | V_at
  | V_question_mark

and binding = var * expr

and view =
  | Type
  | Ty_arrow of ty * ty
  | Ty_pi of var list * ty
  | Var of var
  | Meta of {
      name: string;
      ty: ty option;
    }
  | Wildcard
  | Const of {
      c: K.Expr.t;
      at: bool; (* explicit types? *)
    }
  | App of expr * expr list
  | Lambda of var list * expr
  | Bind of K.Expr.t * var list * expr
  | With of var list * expr
  | Eq of expr * expr
  | Let of binding list * expr

let nopos: position = Position.none

let rec pp_ out (e:expr) : unit =
  match e.view with
  | Type -> Fmt.string out "type"
  | Var v -> Fmt.string out v.v_name
  | Ty_arrow (a,b) ->
    Fmt.fprintf out "%a@ -> %a" pp_atom_ a pp_ b;
  | Ty_pi (vars, bod) ->
    Fmt.fprintf out "(@[pi %a.@ %a@])"
      (pp_list pp_var) vars pp_ bod
  | Const {c;at} ->
    let s = if at then "@" else "" in
    Fmt.fprintf out "%s%a" s K.Expr.pp c
  | App (f,l) -> Fmt.fprintf out "(@[%a@ %a@])" pp_ f (pp_list pp_) l
  | Meta v -> Fmt.fprintf out "?%s" v.name
  | Lambda (vars,bod) ->
    Fmt.fprintf out "(@[\\%a.@ %a@])" (pp_list pp_var_ty) vars pp_ bod
  | Bind (c, vars,bod) ->
    Fmt.fprintf out "(@[%a %a.@ %a@])"
      K.Expr.pp c (pp_list pp_var_ty) vars pp_ bod
  | With (vars,bod) ->
    Fmt.fprintf out "(@[with %a.@ %a@])" (pp_list pp_var_ty) vars pp_ bod
  | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp_ a pp_ b
  | Wildcard -> Fmt.string out "_"
  | Let (bs,bod) ->
    let pp_b out (v,e) : unit = Fmt.fprintf out "@[%s@ = %a@]" v.v_name pp_ e in
    Fmt.fprintf out "(@[let %a in@ %a@])" (pp_list ~sep:" and " pp_b) bs pp_ bod
and pp_atom_ out e =
  match e.view with
  | Type | Var _ | Meta _ | Const _ -> pp_ out e
  | _ -> Fmt.fprintf out "(@[%a@])" pp_ e
and pp_var out v = Fmt.string out v.v_name
and pp_var_ty out (v:var) : unit =
  match v.v_ty with
  | None -> Fmt.string out v.v_name
  | Some ty -> Fmt.fprintf out "(@[%s@ : %a@])" v.v_name pp_ ty

let pp out e = Fmt.fprintf out "`@[%a@]`" pp_ e

module Var = struct
  type t = var
  let make ?kind:(v_kind=V_normal) v_name v_ty : var = {v_name; v_ty; v_kind}

  let pp out v = Fmt.string out v.v_name
  let to_string = Fmt.to_string pp
  let pp_with_ty = pp_var_ty
end

module Expr = struct
  type t = expr
  let mk_ ?(pos=nopos) view : t = {view; pos=pos}

  let[@inline] view e = e.view
  let[@inline] pos e = e.pos
  let pp = pp

  let type_ : t = mk_ Type
  let ty_var ?pos s : t = mk_ ?pos (Var (Var.make s (Some type_)))
  let ty_meta ?pos (s:string) : ty = mk_ ?pos (Meta {ty=Some type_; name=s})
  let ty_arrow ?pos a b : ty = mk_ ?pos (Ty_arrow (a,b))
  let ty_pi ?pos vars bod : ty = match vars with
    | [] -> bod
    | _ -> mk_ ?pos (Ty_pi (vars, bod))

  let var ?pos (v:var) : t = mk_ ?pos (Var v)
  let const ?pos ?(at=false) c : t = mk_ ?pos (Const {c; at})
  let meta ?pos (s:string) ty : t = mk_ ?pos (Meta {ty; name=s})
  let app ?pos (f:t) (l:t list) : t =
    match f.view with
    | App (f1,l1) -> mk_ ?pos (App (f1,l1@l))
    | _ -> mk_ ?pos (App (f,l))
  let let_ ?pos bs bod : t = mk_ ?pos (Let (bs, bod))
  let with_ ?pos vs bod : t = mk_ ?pos (With (vs, bod))
  let lambda ?pos vs bod : t = mk_ ?pos (Lambda (vs, bod))
  let bind ?pos c vs bod : t = mk_ ?pos (Bind (c, vs, bod))
  let eq ?pos a b : t = mk_ ?pos (Eq (a,b))
  let wildcard ?pos () : t = mk_ ?pos Wildcard

  let to_string = Fmt.to_string @@ Fmt.hvbox pp
end

module Goal = struct
  type t = {
    hyps: Expr.t list;
    concl: Expr.t;
  }

  let pp out (self:t) : unit =
    if CCList.is_empty self.hyps then (
      Fmt.fprintf out "@[<h>?- %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[<v>%a@ ?-@ %a@]"
        (pp_list Expr.pp) self.hyps Expr.pp self.concl
    )
  let to_string = Fmt.to_string pp
end

(** {3 Proofs} *)
module Proof = struct
  type t = top with_pos
  and top =
    | Proof_atom of step
    | Proof_steps of {
        lets: pr_let list;
        (** intermediate steps *)
        ret: step;
        (** proof to return *)
      }

  and pr_let =
    | Let_expr of string * expr
    | Let_step of string * step

  and step = step_view with_pos
  and step_view =
    | Pr_apply_rule of string * rule_arg list
    | Pr_sub_proof of t
    | Pr_error of string (* parse error *)

  (** An argument to a rule *)
  and rule_arg =
    | Arg_var of string
    | Arg_step of step

  let rec pp out (self:t) : unit =
    Fmt.fprintf out "@[<hv>@[<hv2>proof@ ";
    begin match self.view with
      | Proof_atom s -> pp_step ~top:true out s
      | Proof_steps {lets; ret} ->
        List.iter
          (function
            | Let_expr (s,e) ->
              Fmt.fprintf out "@[<2>let expr %s =@ %a in@]@ " s Expr.pp e
            | Let_step (s,p) ->
              Fmt.fprintf out "@[<2>let step %s =@ %a in@]@ "
                s (pp_step ~top:true) p)
          lets;
        pp_step ~top:true out ret
    end;
    Fmt.fprintf out "@]@,end@]"

  and pp_step ~top out (s:step) : unit =
    match s.view with
    | Pr_apply_rule (r, []) when top -> Fmt.string out r
    | Pr_apply_rule (r, args) ->
      Fmt.fprintf out "(@[%s@ %a@])" r (pp_list pp_rule_arg) args
    | Pr_sub_proof p -> pp out p
    | Pr_error e -> Fmt.fprintf out "<error %s>" e

  and pp_rule_arg out (a:rule_arg) : unit =
    match a with
    | Arg_var s -> Fmt.string out s
    | Arg_step s -> pp_step ~top:false out s (* always in ( ) *)

  let to_string = Fmt.to_string pp
end

module Meta_stmt = struct
  type t = view with_pos
  and view =
    | Top_def of {
        name: string;
        vars: var list;
        ret: ty;
        body: expr;
      }
    | Top_decl of {
        name: string;
        ty: ty;
      }
    | Top_axiom of {
        name: string;
        thm: expr;
      }
    | Top_goal of {
        goal: Goal.t;
        proof: Proof.t;
      }
    | Top_theorem of {
        name: string;
        goal: Goal.t;
        proof: Proof.t;
      }
    | Top_error of {
        msg: string;
      }

  let pp out (self:t) : unit =
    match self.view with
    | Top_def { name; vars=[]; ret; body } ->
      Fmt.fprintf out "@[<hv>@[<2>def %s : %a :=@ %a@]@ end@]"
        name pp ret pp body
    | Top_def { name; vars; ret; body } ->
      Fmt.fprintf out "@[<hv>@[<2>def %s %a : %a :=@ %a@]@ end@]"
        name (pp_list pp_var_ty) vars pp ret pp body
    | Top_decl { name; ty } ->
      Fmt.fprintf out "@[<hv>@[<2>decl %s :@ %a@]@ end@]"
        name pp ty
    | Top_axiom { name; thm } ->
      Fmt.fprintf out "@[<hv>@[<2>axiom %s :=@ %a@]@ end@]"
        name pp thm
    | Top_goal { goal; proof } ->
      Fmt.fprintf out "@[<hv>@[<2>goal %a@ by %a@]@ end@]"
        Goal.pp goal Proof.pp proof
    | Top_theorem { name; goal; proof } ->
      Fmt.fprintf out "@[<hv>@[<2>theorem %s :=@ %a@ by %a@]@ end@]"
        name Goal.pp goal Proof.pp proof
    | Top_error {msg} -> Fmt.fprintf out "@[<hv><error %s>@]" msg

  let to_string = Fmt.to_string pp

  let make ~pos view : t = {pos; view}
  let def ~pos name vars ret body : t = make ~pos (Top_def {name; ret; vars; body})
  let decl ~pos name ty : t = make ~pos (Top_decl {name; ty})
  let axiom ~pos name e : t = make ~pos (Top_axiom {name; thm=e})
  let goal ~pos goal proof : t = make ~pos (Top_goal {goal; proof})
  let theorem ~pos name g p : t = make ~pos (Top_theorem{name; goal=g; proof=p})
end
