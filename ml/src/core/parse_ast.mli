

open Sigs

module K = Kernel

type position = Position.t
type fixity = Fixity.t

type 'a with_pos = {
  pos: position;
  view: 'a;
}

type expr = private view with_pos

and ty = expr

and var_kind =
  | V_normal
  | V_at
  | V_question_mark

and binding = var * expr

and var = {
  v_name: string;
  v_ty: ty option;
  v_kind: var_kind
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
  | App of expr * expr list
  | Lambda of var list * expr
  | Bind of {
      c: const;
      at: bool; (* explicit types? *)
      vars: var list;
      body: expr;
    }
  | With of var list * expr
  | Eq of expr * expr
  | Let of binding list * expr

module Var : sig
  type t = var
  val make : ?kind:var_kind -> string -> ty option -> var
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

  val pos : t -> Position.t
  val view : t -> view

  val type_ : t
  val ty_var : ?pos:position -> string -> t
  val ty_meta : ?pos:position -> string -> t
  val ty_arrow : ?pos:position -> t -> t -> t
  val ty_pi : ?pos:position -> var list -> t -> t

  val var : ?pos:position -> var -> t
  val const : ?pos:position -> ?at:bool -> const -> t
  val of_expr : ?pos:position -> ?at:bool -> K.Expr.t -> t
  val meta : ?pos:position -> string -> ty option -> t
  val app : ?pos:position -> t -> t list -> t
  val let_ : ?pos:position -> (var * t) list -> t -> t
  val with_ : ?pos:position -> var list -> t -> t
  val lambda : ?pos:position -> var list -> t -> t
  val bind : ?pos:position -> ?at:bool -> const -> var list -> t -> t
  val eq : ?pos:position -> t -> t -> t
  val wildcard : ?pos:position -> unit -> t
end

(** {2 Goal}

    A goal is a conjecture that reflects what the final theorem should
    look like. *)
module Goal : sig
  type t = {
    hyps: Expr.t list;
    concl: Expr.t;
  }

  include PP with type t := t
end

(** {2 Proofs} *)
module Proof : sig
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

  include PP with type t := t
end

(* TODO
(** {2 Expressions to construct proofs, tactics, etc.} *)
module Meta_expr : sig

  type mexpr = private mexpr_view with_pos

  and mexpr_view =
    | E_expr of Expr.t
    | E_goal of Goal.t
    | E_proof of proof
    | E_tactic of tactic

  and tactic = private tactic_view with_pos

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

type top_statement = private top_statement_view with_pos
and top_statement_view =
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
  | Top_error of {
      msg: string; (* parse error *)
    }
  (* TODO  | Top_def_ty of string *)
  (* TODO: | Top_def_proof_rule *)
  (* TODO: | Top_def_rule *)
  (* TODO: | Top_def_tactic *)

module Top_stmt : sig
  type t = top_statement

  include Sigs.PP with type t := t

  val pos : t -> position
  val view : t -> top_statement_view
  val make : pos:position -> top_statement_view -> t

  val def : pos:position -> string -> var list -> ty -> expr -> t
  val decl : pos:position -> string -> ty -> t
  val fixity : pos:position -> string -> fixity -> t
end

module Env : sig
  type t

  val create : K.Ctx.t -> t
  val copy : t -> t
  val ctx : t -> K.Ctx.t

  val declare : t -> string -> const
  val declare' : t -> string -> unit
  val declare_fixity : t -> string -> fixity -> unit

  val find : t -> string -> (const * fixity) option

  val process : t -> Top_stmt.t -> unit
  (** Process declaration/definition from the statement *)

  val bool : t -> const
  val eq : t -> const
end
