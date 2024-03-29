type loc = Loc.t

type 'a with_loc = 'a With_loc.t = {
  loc: Loc.t;
  view: 'a;
}

let pp_with_loc ppx out x = ppx out x.With_loc.view

let mk ~loc x : _ with_loc = { With_loc.view = x; loc }

module type PARSER_PARAM = sig
  val ctx : Local_loc.ctx
end

type const =
  | C_int of int
  | C_string of string
  | C_bool of bool
  | C_atom of string
  | C_unit
[@@deriving show { with_path = false }]

type binop =
  | Plus
  | Minus
  | Times
  | Div
  | Eq
  | Neq
  | And
  | Or
  | Leq
  | Lt
  | Geq
  | Gt
[@@deriving show { with_path = false }]

type unop =
  | Not
  | Uminus
[@@deriving show { with_path = false }]

type var = string with_loc [@@deriving show { with_path = false }]

(** Logical binder *)
type lbinder =
  | L_lambda
  | L_with
  | L_other of var
[@@deriving show { with_path = false }]

type statement = statement_view with_loc
(** Toplevel statement *)

and statement_view =
  | S_fn of var * var list * block
  | S_eval of expr
(* TODO: theorem, structured proofs, etc. *)

and expr = expr_view with_loc
(** Meta level expression *)

and expr_view =
  | E_var of var
  | E_app of var * expr list
  | E_array_lit of expr list
  | E_binop of binop * expr * expr
  | E_unop of unop * expr
  | E_const of const
  | E_logic of lexpr
  | E_block of block
  | E_if of {
      test: expr;
      then_: block;
      elseif: (expr * block) list;
      else_: block option;
    }
[@@deriving show { with_path = false }]

and lexpr = lexpr_view with_loc
(** Logical expr *)

and lexpr_view =
  | L_var of var
  | L_app of lexpr * lexpr list
  | L_bind of {
      binder: lbinder;
      bs: (var list * lexpr option) list;
      body: lexpr;
    }
  | L_escape of expr (* inject result of computation *)
[@@deriving show { with_path = false }]

and block = block_view with_loc
(** Meta-level block (composite expression) *)

and block_view = { bl_items: block_item list }

and block_item = block_item_view with_loc

and block_item_view =
  | Bl_let of var * expr
  | Bl_var of var * expr
  | Bl_assign of var * expr
  | Bl_eval of expr
  | Bl_while of expr * block
  | Bl_return of expr
  | Bl_break
  | Bl_continue (* TODO: [for x = 1,n { }] à la lua *)
  | Bl_block of block
[@@deriving show { with_path = false }]

type top = statement list [@@deriving show]
