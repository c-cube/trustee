

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

type expr = private view with_loc

and ty = expr

and var_kind =
  | V_normal
  | V_at
  | V_question_mark

and binding = var * expr

and var = {
  v_name: string;
  v_ty: ty option;
  v_kind: var_kind;
  v_loc: location;
}

and const = private
  | C_local of string (* not resolved yet *)
  | C_k of K.expr

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
      c: const;
      at: bool; (* explicit types? *)
    }
  | App of expr * expr
  | Lambda of var list * expr
  | Bind of {
      c: const;
      c_loc: location;
      at: bool; (* explicit types? *)
      vars: var list;
      body: expr;
    }
  | With of var list * expr
  | Eq of expr * expr
  | Let of binding list * expr

type subst = (string * expr) list

module Var : sig
  type t = var
  val make : ?kind:var_kind -> loc:location -> string -> ty option -> var
  include PP with type t := t
  val pp_with_ty : t Fmt.printer
end

module Const : sig
  type t = const
  include PP with type t := t
  val of_expr : K.Expr.t -> t
end

(** {2 Logical expressions} *)
module Expr : sig
  type t = expr

  include PP with type t := t
  val pp_quoted : t Fmt.printer

  val loc : t -> location
  val view : t -> view

  val type_ : t
  val ty_var : loc:location -> string -> t
  val ty_meta : loc:location -> string -> t
  val ty_arrow : loc:location -> t -> t -> t
  val ty_pi : loc:location -> var list -> t -> t

  val var : loc:location -> var -> t
  val const : loc:location -> ?at:bool -> const -> t
  val of_expr : loc:location -> ?at:bool -> K.Expr.t -> t
  val meta : loc:location -> string -> ty option -> t
  val app : t -> t -> t
  val app_l : t -> t list -> t
  val let_ : loc:location -> (var * t) list -> t -> t
  val with_ : loc:location -> var list -> t -> t
  val lambda : loc:location -> var list -> t -> t
  val bind :
    loc:location -> c_loc:location -> ?at:bool ->
    const -> var list -> t -> t
  val eq : loc:location -> t -> t -> t
  val wildcard : loc:location -> unit -> t
end

(** {2 Substitution} *)
module Subst : sig
  type t = subst
  include PP with type t := t
end

(** {2 Goal}

    A goal is a conjecture that reflects what the final theorem should
    look like. *)
module Goal : sig
  type t = private {
    hyps: Expr.t list;
    concl: Expr.t;
  }

  val make : Expr.t list -> Expr.t -> t
  val make_nohyps : Expr.t -> t

  include PP with type t := t
end

(** {2 Proofs} *)
module Proof : sig
  type t = private top with_loc
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
    | Arg_var of string
    | Arg_step of step
    | Arg_expr of expr
    | Arg_subst of subst

  type rule_signature = TyRule.signature

  include PP with type t := t
  val pp_pr_let : pr_let Fmt.printer
  val pp_rule_arg : rule_arg Fmt.printer
  val pp_rule_signature : rule_signature Fmt.printer

  val view : t -> top
  val loc : t -> location

  val s_view : step -> step_view
  val s_loc : step -> location

  val make : loc:location -> pr_let list -> step -> t
  val let_expr : string with_loc -> expr -> pr_let
  val let_step : string with_loc -> step -> pr_let

  val step_apply_rule : loc:location -> string with_loc -> rule_arg list -> step
  val step_subproof : loc:location -> t -> step
  val step_error : loc:location -> unit Fmt.printer -> step

  val arg_var : string -> rule_arg
  val arg_step : step -> rule_arg
  val arg_expr : expr -> rule_arg
  val arg_subst : subst -> rule_arg
end

(* TODO
(** {2 Expressions to construct proofs, tactics, etc.} *)
module Meta_expr : sig

  type mexpr = private mexpr_view with_loc

  and mexpr_view =
    | E_expr of Expr.t
    | E_goal of Goal.t
    | E_proof of proof
    | E_tactic of tactic

  and tactic = private tactic_view with_loc

  and tactic_view =
    | Tac_apply of string * mexpr list
    | Tac_have_in of string * tactic * tactic
    | Tac_fail
    | Tac_proof of proof
    | Tac_apply_thm of string

  (** A toplevel proof, or tactic with an optional cached proof along with it*)
  type toplevel_proof =
    | TP_proof of proof
    | TP_tactic of {
        stored_proof: proof option;
        tac: tactic;
    }

  module Expr : sig
    type t = mexpr
    include PP with type t := t
  end

  (** {3 Tactic term} *)
  module Tactic : sig
    type t = tactic
    include PP with type t := t
  end
end
   *)

(** {2 Statements} *)

type top_statement = private top_statement_view with_loc
and top_statement_view =
  | Top_enter_file of string
  | Top_def of {
      name: string;
      th_name: string option;
      vars: var list;
      ret: ty option;
      body: expr;
    }
  | Top_decl of {
      name: string;
      ty: ty;
    }
  | Top_fixity of {
      name: string;
      fixity: fixity;
    }
  | Top_axiom of {
      name: string;
      thm: expr;
    }
  | Top_goal of {
      goal: Goal.t;
      proof: Proof.t;
      (* TODO: instead, Meta_expr.toplevel_proof; *)
    }
  | Top_theorem of {
      name: string;
      goal: Goal.t;
      proof: Proof.t;
      (* TODO: instead, Meta_expr.toplevel_proof; *)
    }
  | Top_show of string
  | Top_show_expr of expr
  | Top_show_proof of Proof.t
  | Top_error of {
      msg: unit Fmt.printer; (* parse error *)
    }
  (* TODO  | Top_def_ty of string *)
  (* TODO: | Top_def_proof_rule *)
  (* TODO: | Top_def_rule *)
  (* TODO: | Top_def_tactic *)

module Top_stmt : sig
  type t = top_statement

  include Sigs.PP with type t := t

  val loc : t -> location
  val view : t -> top_statement_view
  val make : loc:location -> top_statement_view -> t

  val enter_file : loc:location -> string -> t
  val def : loc:location -> string ->
    th_name: string option -> var list -> ty option -> expr -> t
  val decl : loc:location -> string -> ty -> t
  val fixity : loc:location -> string -> fixity -> t
  val axiom : loc:location -> string -> expr -> t
  val goal : loc:location -> Goal.t -> Proof.t -> t
  val theorem : loc:location -> string -> Goal.t -> Proof.t -> t
  val show : loc:location -> string -> t
  val show_expr : loc:location -> expr -> t
  val show_proof : loc:location -> Proof.t -> t
  val error : loc:location -> unit Fmt.printer -> t
end

module Env : sig
  type t

  val create : K.Ctx.t -> t
  val copy : t -> t
  val ctx : t -> K.Ctx.t

  val declare : t -> string -> const
  val declare' : t -> string -> unit
  val declare_fixity : t -> string -> fixity -> unit

  val declare_rule : t -> string -> Proof.rule_signature -> unit

  val find_const : t -> string -> (const * fixity) option
  val find_rule: t -> string -> Proof.rule_signature option

  val process : t -> Top_stmt.t -> unit
  (** Process declaration/definition from the statement *)

  val bool : t -> const
  val eq : t -> const
end

