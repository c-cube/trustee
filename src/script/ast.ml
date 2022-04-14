
type loc = Loc.t
type 'a with_loc = 'a With_loc.t

let mk ~loc x : _ with_loc = {With_loc.view=x; loc}

module type PARSER_PARAM = sig
  val ctx : Local_loc.ctx
end

type const =
  | C_int of int
  | C_string of string
  | C_bool of bool
  | C_unit

type binop =
  | Plus
  | Minus
  | Times
  | Div
  | Leq
  | Lt
  | Geq
  | Gt

type var = string with_loc

type expr = expr_view with_loc
and expr_view =
  | E_var of var
  | E_app of var * expr list
  | E_op of binop * expr * expr
  | E_const of const

type statement = statement_view with_loc
and statement_view =
  | S_fn of var * var list * block
  | S_eval of expr
  (* TODO: theorem, structured proofs, etc. *)

and block = block_view with_loc
and block_view = {
  bl_items: block_item list;
}

and block_item =
  | S_let of var * expr
  | S_var of var * expr
  | S_eval of expr
  | S_while of expr * block
  | S_return of expr
  | S_break
  | S_continue
    (* TODO: [for x = 1,n { }] à la lua *)
  | S_block of block
