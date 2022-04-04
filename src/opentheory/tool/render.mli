
(** Render to HTML *)

open Trustee_opentheory.Common_

module Config : sig
  type t = {
    open_namespaces: string list;
    (** Do not print prefixes for these namespaces *)
  }

  val make :
    ?open_namespaces:string list ->
    unit -> t
end

val expr_to_html : ?config:Config.t -> K.Expr.t -> Html.elt

val thm_to_html : ?config:Config.t -> K.Thm.t -> Html.elt

val const_to_html : K.Const.t -> Html.elt

val subst_to_html : K.Subst.t -> Html.elt

val theory_to_html : ?config:Config.t -> K.Theory.t -> Html.elt
