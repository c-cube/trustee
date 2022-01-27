
type 'a t
(** A parser of values of type ['a]. *)

val run : Token.t Lstream.t -> 'a t -> ('a, Error.t) result
(** Run the parser *)

val run_exn : Token.t Lstream.t -> 'a t -> 'a
(** Run the parser.
    @raise Error.E in case of error. *)

(** {2 Core combinators} *)

type message = unit -> string

val return : 'a -> 'a t
val fail : Error.t -> _ t
val fail_str : string -> _ t
val fail_strf : ('a, Format.formatter, unit, 'b t) format4 -> 'a

module Infix : sig
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( *> ) : _ t -> 'a t -> 'a t
  val ( <* ) : 'a t -> _ t -> 'a t
end

include module type of Infix

val exact : ?msg:message -> Token.t -> Loc.t t
val exact' : ?msg:message -> Token.t -> unit t

val next : (Token.t * Loc.t) t
(** Read and consume next token *)

val loc : Loc.t t
(** Location of next token. Does not consume the token. *)

val token_if : ?msg:message -> (Token.t -> bool) -> (Token.t * Loc.t) t
(** [token_if f] parses a token that is accepted by [f], and consumes it. *)

val switch_next :
  (Token.t -> Loc.t -> [`consume | `keep] * 'a t) ->
  'a t
(** [switch_next f] calls [f tok loc] where [tok] is the next token,
    with location [loc].
    If [f tok = `consume, p], it consumes [tok] before becoming [p],
    else [f tok = `keep, p] it doesn't consume [tok]. It becomes [p] in both cases. *)

val (<|>) : (Token.t * 'a t) -> 'a t -> 'a t
(** [(tok, p1) <|> p2] consumes [tok] if it's the next token and
      becomes [p1], or doesn't consume the next token and becomes [p2]. *)

val try_ : 'a t -> ('a, Error.t) result t
(** Reify errors *)

val parsing : (Error.t -> Error.t) -> 'a t -> 'a t
(** [parsing wrap p] behaves like [p], but errors raised by [p]
    are modified using [wrap]. Typically, {!Error.wrap}
    or {!Error.wrapf} can be used to provide context. *)

(** {2 Helpers} *)

val lbrace : ?msg:message -> unit -> unit t
val rbrace : ?msg:message -> unit -> unit t
val lparen : ?msg:message -> unit -> unit t
val rparen : ?msg:message -> unit -> unit t
val semi : ?msg:message -> unit -> unit t
val eoi : msg:message -> unit -> unit t

val sym : string t
