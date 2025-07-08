module K = Trustee_core.Kernel

type 'a or_error = 'a Trustee_core.Error.or_error
type input

module Input : sig
  type t = input

  val of_string : string -> t
  val of_chan : in_channel -> t
end

type t
(** {2 Virtual Machine} *)

val create : ?progress_bar:bool -> K.ctx -> in_scope:K.Theory.t list -> t
(** [create ctx ~in_scope] makes a new VM with given context, and the theories
    [in_scope] to look up external constants from.
    @param progress_bar
      if true, a progress bar will be printed on stdout as articles are checked.
*)

include PP with type t := t

val pp_stats : t Fmt.printer
val article : t -> Article.t
val clear_article : t -> unit
val clear_dict : t -> unit
val has_empty_stack : t -> bool

val parse_and_check_art_exn :
  name:string -> t -> input -> K.Theory.t * Article.t

val parse_and_check_art :
  name:string -> t -> input -> (K.Theory.t * Article.t) or_error
