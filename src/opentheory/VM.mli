
module K = Trustee_core.Kernel

type input

module Input : sig
  type t = input

  val of_string : string -> t
  val of_chan : in_channel -> t
end

(** {2 Virtual Machine} *)
type t

val create : ?progress_bar:bool -> K.ctx -> t

include PP with type t := t
val pp_stats: t Fmt.printer

val article : t -> Article.t
val clear_article : t -> unit

val clear_dict : t -> unit

val has_empty_stack : t -> bool

val parse_and_check_art_exn :
  t -> input -> Article.t

val parse_and_check_art :
  t -> input -> Article.t or_error

