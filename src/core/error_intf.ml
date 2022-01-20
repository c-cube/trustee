
open Sigs

module type S = sig
  type loc
  type t

  exception E of t

  type 'a or_error = ('a, t) result

  val raise : t -> 'a

  val make : ?loc:loc -> string -> t
  val make' : ?loc:loc -> (unit -> string) -> t
  val makef : ?loc:loc -> ('a, Format.formatter, unit, t) format4 -> 'a
  val of_exn : exn -> t

  val wrap' : ?loc:loc -> (unit -> string) -> t -> t
  val wrap : ?loc:loc -> string -> t -> t
  (** [wrap msg e] makes a composite error that gives context to [e]. *)

  val wrapf : ?loc:loc -> ('a, Format.formatter, unit, t -> t) format4 -> 'a

  val msg : t -> string
  val msg' : t -> (unit -> string)
  val loc : t -> loc option
  val ctx_of : t -> t option
  val unwrap_ctx : t -> t * t list

  val unwrap : ('a, t) result -> 'a
  (** Obtain result, or {!raise} error *)

  val unwrap_opt : string -> 'a option -> 'a
  val unwrap_opt' : (unit -> string) -> 'a option -> 'a

  val fail : ?loc:loc -> string -> 'a
  (** Build error and {!raise} it *)

  val failf :
    ?loc:loc ->
    ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> 'b

  val guard : (t -> t) -> (unit -> 'a) -> 'a
  (** [guard wrap f] runs [f()], and wraps the error with [wrap] if
      it fails.

      Typical usage: [Error.guard (Error.wrapf "oh no %d" 42) @@ fun () -> …]
  *)

  val pp : t Fmt.printer
end

module type LOC = sig
  type t
  val pp : t Fmt.printer
end
