

open Sigs

module K = Kernel

type position = Position.t

type expr = private {
  pos: position;
  view: view;
}

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

module Var : sig
  type t = var
  val make : ?kind:var_kind -> string -> ty option -> var
  include PP with type t := t
  val pp_with_ty : t Fmt.printer
end

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
  val const : ?pos:position -> ?at:bool -> K.Expr.t -> t
  val meta : ?pos:position -> string -> ty option -> t
  val app : ?pos:position -> t -> t list -> t
  val let_ : ?pos:position -> (var * t) list -> t -> t
  val with_ : ?pos:position -> var list -> t -> t
  val lambda : ?pos:position -> var list -> t -> t
  val bind : ?pos:position -> K.Expr.t -> var list -> t -> t
  val eq : ?pos:position -> t -> t -> t
  val wildcard : ?pos:position -> unit -> t
end
