
(** {1 Evaluate theories} *)

open Common_
type 'a or_error = 'a Trustee_core.Error.or_error

(** {2 Callbacks for the checking process} *)

class type callbacks = object
  method start_theory : string -> unit
  method done_theory : string -> ok:bool -> time_s:float -> unit
  method start_article : string -> unit
  method done_article : string -> Article.t -> time_s:float -> unit
end

class default_callbacks : callbacks
class print_callbacks : callbacks

(** {2 Evaluation of theories} *)

type state

val create :
  ?cb:callbacks ->
  ?progress_bar:bool ->
  ctx:K.ctx ->
  idx:Idx.t ->
  unit ->
  state

type eval_info = {
  info: string;
  time: float;
  sub: (string * eval_info) list;
}

val eval_info_to_html : eval_info -> Html.elt

val eval_theory :
  state ->
  string ->
  (K.Theory.t * eval_info) or_error
(** [eval_theory st name] builds and
    returns the theory with given name from the index.
    The theory will be cached, as will any theory it depends on. *)
