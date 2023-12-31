(** Main parser.

    This is the parser for files, containing all top declarations,
    logical expressions (see {!Expr_parser}), meta definitions, etc.

    We use a S-expression based syntax because life is short, and it
    looks good without having to make any syntactic decisions.
*)

open Common_
module A = Parse_ast
module SD = Sexp_decode

type t

val create : src_string:string -> notation:Notation.Ref.t -> unit -> t

type 'a parser = t -> 'a SD.t

type 'a or_error = ('a, Loc.t * Error.t) result

module Or_error : sig
  type 'a t = 'a or_error

  val get_exn : 'a t -> 'a

  val sequence_l : 'a t list -> 'a list t
end

val run : t -> filename:string -> string -> 'a parser -> 'a or_error list

val run_exn : t -> filename:string -> string -> 'a parser -> 'a list

module P_expr : sig
  val top : A.Expr.t parser
end

module P_subst : sig
  val top : A.Subst.t parser
end

val top : A.Top.t parser

val parse_string :
  ?filename:string ->
  notation:Notation.Ref.t ->
  string ->
  'a parser ->
  'a or_error list

val parse_string_exn :
  ?filename:string -> notation:Notation.Ref.t -> string -> 'a parser -> 'a list
