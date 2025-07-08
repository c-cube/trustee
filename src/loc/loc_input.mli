type view = private
  | File of string
  | String of string

type t

val file : string -> t
val string : string -> t
val view : t -> view
val pp : t Fmt.printer
