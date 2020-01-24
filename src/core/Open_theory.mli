
(** {1 Parser for OpenTheory files} *)

module Expr = Kernel_of_trust.Expr
module Thm = Kernel_of_trust.Thm
module Fmt = CCFormat

type 'a gen = unit -> 'a option
type thm = Thm.t

type article = {
  assumptions: thm list;
  theorems: thm list;
}

val parse_gen : string gen -> (article, string) result

val parse_gen_exn : string gen -> article
(** Try to parse the article.
    @raise Error.Error in case of problem. *)

val parse : string -> (article, string) result

val parse_exn : string -> article
(** Try to parse the article.
    @raise Error.Error in case of problem. *)

module Article : sig
  type t = article

  val pp : t Fmt.printer
end
