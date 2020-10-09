
(* This file is free software. See file "license" for more details. *)

(** {1 Parsing Combinators}

    Inspired from Angstrom and CCParse *)

open Sigs

(** {2 Input} *)

type position = Position.t

(** {2 Combinators} *)

type offset

(** The main type for parse errors *)
type error = {
  offset: offset;
  pos: position lazy_t;
  msg: unit -> string;
  parsing: string list;
}

type 'a or_error = ('a, error) result

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

val (<**>) : 'a t -> 'b t -> ('a * 'b) t
(** Product  *)

val ( *>) : _ t -> 'a t -> 'a t
(** [a *> b] parses [a], then parses [b] into [x], and returns [x]. The
    results of [a] is ignored. *)

val try_bind :
  'a t ->
  ok:('a -> 'b t) ->
  err:(error -> 'b t) ->
  'b t
(** Attempt a parse, and call one of the two callbacks.
    Given [try_bind p ~ok ~err], two cases:
    - if [p] succeeds with value [x], then [ok x] is used to parse
      the rest of the string.
    - if [p] fails with error [e], no input is consumed and
      [err e] is called to fail or attempt recovery.

    For example, [err] can use {!save_error} to emit errors at the end,
    and then try to recover by skipping input until a clear break
    such as ";;" or "\n\n" is met.
*)

val save_error : error -> unit t
(** Save error in the state. Errors will be available in {!parse_with_errors}. *)

val fail : string -> 'a t
(** [fail msg] fails with the given message. It can trigger a backtrack. *)

val failf: ('a, Format.formatter, unit, 'b t) format4 -> 'a
(** [Format.sprintf] version of {!fail}. *)

val parsing : string -> 'a t -> 'a t
(** [parsing s p] behaves the same as [p], with the information that
    we are parsing [s], if [p] fails. *)

val eoi : unit t
(** Expect the end of input, fails otherwise. *)

val lookahead : 'a t -> 'a t
(** [lookahead p] behaves like [p], but does not consume any input *)

val nop : unit t
(** Succeed with [()]. *)

val guard : ?msg:string -> ('a -> bool) -> 'a t -> 'a t
(** [guard f p] parses the same as [p], but after parsing [x]
    it fails if [f x] is false *)

val char_exact : char -> char t
(** [char c] parses the character [c] and nothing else. *)

val char_skip : unit t
(** Skip one char. Fails on EOF. *)

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

val (<||>) : ('a t * ('a -> 'b t)) -> 'b t -> 'b t
(** Infix synonym to {!if_} *)

val cond : (_ t * 'a t) list -> 'a t -> 'a t
(** [cond l else_] tries each pair [cond_i, br_i]
    in the list [l]. If [cond_i] succeeds, the whole parser becomes [br_i]
    without backtracking. {!lookahead} can be used to avoid consuming input
    on the condition.
    If all fail, [else_] is called. *)

val (<?>) : 'a t -> string -> 'a t
(** [a <?> msg] behaves like [a], but if [a] fails
    it fails with [msg] instead.
    Useful as the last choice in a series of [<|>]:
    [a <|> b <|> c <?> "expected a|b|c"]. *)

val ignore : 'a t -> unit t
(** Ignore the output *)

val suspend : (unit -> 'a t) -> 'a t
(** [suspend f] is  the same as [f ()], but evaluates [f ()] only
    when needed. *)

val string_exact : string -> unit t
(** [string s] parses exactly the string [s], and nothing else. *)

val keyword : string -> unit t
(** [keyword s] parses exactly [s] followed by one whitespace that
    is then discarded. *)

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

val cur_pos : Position.t lazy_t t
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

val parse : 'a t -> string -> 'a or_error
(** [parse p s] applies [p] on the input, and returns [Ok x] if
    [p] succeeds with [x], or [Error s] otherwise. *)

val parse_with_errors : 'a t -> string -> ('a or_error * error list)
(** Same as {!parse}, except all errors called with {!save_error}
    are also returned on the side. *)

val parse_exn : 'a t -> string -> 'a
(** Unsafe version of {!parse}.
    @raise Parse_error if it fails. *)

(** {2 Infix} *)

module Infix : sig
  val (>|=) : 'a t -> ('a -> 'b) -> 'b t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (<*>) : ('a -> 'b) t -> 'a t -> 'b t
  val (<**>) : 'a t -> 'b t -> ('a * 'b) t
  val (<* ) : 'a t -> _ t -> 'a t
  val ( *>) : _ t -> 'a t -> 'a t
  val (<|>) : 'a t -> 'a t -> 'a t
  val (<||>) : ('a t * ('a -> 'b t)) -> 'b t -> 'b t
  val (<?>) : 'a t -> string -> 'a t
end
