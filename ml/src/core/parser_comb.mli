
(* This file is free software. See file "license" for more details. *)

(** {1 Parsing Combinators}

    Inspired from Angstrom and CCParse *)

open Sigs

(** {2 Input} *)

type position = Position.t
type state

module State : sig
  type t = state
  val create : string -> t
end

(** {2 Combinators} *)

type offset

type error = {
  offset: offset;
  pos: position;
  msg: string;
  parsing: string list;
}

exception Parse_error of error

module Err : sig
  type t = error
  include PP with type t := t
end

type 'a t
(** Parser returning values of type ['a] *)

val return : 'a -> 'a t
(** Always succeeds, without consuming its input. *)

val pure : 'a -> 'a t

val (>|=) : 'a t -> ('a -> 'b) -> 'b t
(** Map. *)

val map : ('a -> 'b) -> 'a t -> 'b t

val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

val map3 : ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t

val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
(** Monadic bind.
    [p >>= f] results in a new parser which behaves as [p] then,
    in case of success, applies [f] to the result. *)

val (<*>) : ('a -> 'b) t -> 'a t -> 'b t
(** Applicative. *)

val (<* ) : 'a t -> _ t -> 'a t
(** [a <* b] parses [a] into [x], parses [b] and ignores its result,
    and returns [x]. *)

val product : 'a t -> 'b t -> ('a * 'b) t
(** Parse a pair *)

val ( *>) : _ t -> 'a t -> 'a t
(** [a *> b] parses [a], then parses [b] into [x], and returns [x]. The
    results of [a] is ignored. *)

val fail : string -> 'a t
(** [fail msg] fails with the given message. It can trigger a backtrack. *)

val failf: ('a, Format.formatter, unit, 'b t) format4 -> 'a
(** [Format.sprintf] version of {!fail}. *)

val parsing : string -> 'a t -> 'a t
(** [parsing s p] behaves the same as [p], with the information that
    we are parsing [s], if [p] fails. *)

val eoi : unit t
(** Expect the end of input, fails otherwise. *)

val nop : unit t
(** Succeed with [()]. *)

val char_exact : char -> char t
(** [char c] parses the character [c] and nothing else. *)

val char : char t
(** Return current char. Fails on EOF *)

val char_if : ?msg:string -> (char -> bool) -> char t
(** [char_if f] parses a character [c] if [f c = true]. *)

val chars_if : (char -> bool) -> string t
(** [chars_if f] parses a string of chars that satisfy [f]. *)

val chars_if_len : ?msg:string -> int -> (char -> bool) -> string t
(** [chars_if_len n f] parses a string of length [n] of chars that satisfy [f]. *)

val chars1_if : ?msg:string -> (char -> bool) -> string t
(** Like {!chars_if}, but only non-empty strings. *)

val endline : char t
(** Parse '\n'. *)

val space : char t
(** Tab or space. *)

val white : char t
(** Tab or space or newline. *)

val skip_chars : (char -> bool) -> unit t
(** Skip 0 or more chars satisfying the predicate. *)

val skip_space : unit t
(** Skip ' ' and '\t'. *)

val skip_white : unit t
(** Skip ' ' and '\t' and '\n'. *)

val is_alpha : char -> bool
(** Is the char a letter? *)

val is_num : char -> bool
(** Is the char a digit? *)

val is_alpha_num : char -> bool
(** Is the char a letter or a digit? *)

val is_space : char -> bool
(** True on ' ' and '\t'. *)

val is_white : char -> bool
(** True on ' ' and '\t' and '\n'. *)

val (<|>) : 'a t -> 'a t -> 'a t
(** [a <|> b] tries to parse [a], and if [a] fails, behaves like [b]. *)

val if_ : 'a t -> ('a -> 'b t) -> 'b t -> 'b t
(** [if_ c ptrue pfalse] tries to parse [c].
    If [c] succeeds, it calls [ptrue] without any backtracking point,
    otherwise it becomes [pfalse] *)

val cond : (_ t * 'a t) list -> 'a t -> 'a t
(** [cond l else_] tries each pair [cond_i, br_i]
    in the list [l]. If [cond_i] succeeds, it becomes [br_i]
    without backtracking.
    If all fail, [else_] is called. *)

val (<?>) : 'a t -> string -> 'a t
(** [a <?> msg] behaves like [a], but if [a] fails
    it fails with [msg] instead.
    Useful as the last choice in a series of [<|>]:
    [a <|> b <|> c <?> "expected a|b|c"]. *)

val suspend : (unit -> 'a t) -> 'a t
(** [suspend f] is  the same as [f ()], but evaluates [f ()] only
    when needed. *)

val string_exact : string -> unit t
(** [string s] parses exactly the string [s], and nothing else. *)

val many : 'a t -> 'a list t
(** [many p] parses a list of [p], eagerly (as long as possible). *)

val many1 : ?msg:string -> 'a t -> 'a list t
(** Parse a non-empty list. *)

val skip : _ t -> unit t
(** [skip p] parses zero or more times [p] and ignores its result. *)

val sep : by:_ t -> 'a t -> 'a list t
(** [sep ~by p] parses a list of [p] separated by [by]. *)

val sep1 : by:_ t -> 'a t -> 'a list t
(** [sep1 ~by p] parses a non empty list of [p], separated by [by]. *)

val fix : ('a t -> 'a t) -> 'a t
(** Fixpoint combinator. *)

val cur_pos : Position.t t
(** Reflect the current position. *)

val int : int t
(** Parse an int. *)

val ident_with_sym : (char -> bool) -> string t
(** Non empty string of alpha num and symbols, start with alpha. *)

val ident : string t
(** Non empty string of alpha num or '_', start with alpha. *)

val list : ?start:string -> ?stop:string -> ?sep:string -> 'a t -> 'a list t
(** [list p] parses a list of [p], with the OCaml conventions for
    start token "[", stop token "]" and separator ";".
    Whitespace between items are skipped. *)

(** {2 Parse}
    Those functions have a label [~p] on the parser, since 0.14.
*)

type 'a or_error = ('a, error) result

val parse : 'a t -> state -> 'a or_error
(** [parse p st] applies [p] on the input, and returns [Ok x] if
    [p] succeeds with [x], or [Error s] otherwise. *)

val parse_exn : 'a t -> state -> 'a
(** Unsafe version of {!parse}.
    @raise Parse_error if it fails. *)

val parse_string : 'a t -> string -> 'a or_error
(** Specialization of {!parse} for string inputs. *)

val parse_string_exn : 'a t -> string -> 'a
(** @raise Parse_error if it fails. *)

(** {2 Infix} *)

module Infix : sig
  val (>|=) : 'a t -> ('a -> 'b) -> 'b t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (<*>) : ('a -> 'b) t -> 'a t -> 'b t
  val (<* ) : 'a t -> _ t -> 'a t
  val ( *>) : _ t -> 'a t -> 'a t
  val (<|>) : 'a t -> 'a t -> 'a t
  val (<?>) : 'a t -> string -> 'a t
end
