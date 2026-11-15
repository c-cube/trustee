(** Render to HTML *)

open Trustee_opentheory.Common_

module Config : sig
  type t = {
    open_namespaces: string list;
        (** Do not print prefixes for these namespaces *)
    open_all_namespaces: bool;  (** Always strip prefix *)
  }

  val make :
    ?open_namespaces:string list -> ?open_all_namespaces:bool -> unit -> t
end

val expr_to_html : ?config:Config.t -> K.Expr.t -> Html.elt
val thm_to_html : ?config:Config.t -> K.Thm.t -> Html.elt
val const_to_html : ?config:Config.t -> K.Const.t -> Html.elt
val const_head_html : ?config:Config.t -> K.Const.t -> Html.elt
val const_def_to_html : ?config:Config.t -> K.Ctx.t -> K.Const.t -> Html.elt
val island : kind:string -> blob:string -> off:int -> Html.elt

val theory_to_html :
  ?config:Config.t ->
  ?make_proof_link:(int -> string) ->
  blob:string ->
  const_offsets:int option array ->
  seq_offsets:int option array ->
  K.Theory.t ->
  Html.elt
