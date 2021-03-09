
(** {1 Evaluate theories} *)

module K = Trustee_core.Kernel

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

val eval_theory :
  state ->
  string ->
  K.Theory.t or_error
(** [eval_theory st name] builds and
    returns the theory with given name from the index.
    The theory will be cached, as will any theory it depends on. *)
