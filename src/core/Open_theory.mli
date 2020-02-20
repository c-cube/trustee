
(** {1 Parser for OpenTheory files} *)

module Fmt = CCFormat
type 'a gen = unit -> 'a option

module Make(C : Core.S) : sig
  open C.KoT
  type thm = Thm.t

  module Defs : sig
    type t
    val create : unit -> t
  end

  type article = {
    defs: Defs.t;
    assumptions: thm list;
    theorems: thm list;
  }

  val parse_gen : Defs.t -> string gen -> (article, string) result

  val parse_gen_exn : Defs.t -> string gen -> article
  (** Try to parse the article.
      @raise Error.Error in case of problem. *)

  val parse : Defs.t -> string -> (article, string) result

  val parse_exn : Defs.t -> string -> article
  (** Try to parse the article.
      @raise Error.Error in case of problem. *)

  module Article : sig
    type t = article

    val pp : t Fmt.printer
  end
end
