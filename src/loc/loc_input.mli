type view = private
  | String of string

type t
val string : string -> t

val view : t -> view
val pp : t Fmt.printer
