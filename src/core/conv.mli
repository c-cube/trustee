
(** {1 Converters} *)

open Sigs
module K = Kernel
module E = K.Expr

(** Result of a rewriting operation *)
type rw_step =
  | Same
  | Rw_step of K.thm
    (** A theorem [A |- a=b] where [a] is the initial term, and [b] the result. *)

val pp_rw_step : rw_step Fmt.printer

type t = K.ctx -> K.expr -> rw_step
(** Converter: takes a term and returns a possible rewrite theorem for it *)

val empty : t
(** Converter that does nothing *)

val apply : t -> K.ctx -> K.expr -> K.thm
(** [apply conv ctx e] applies [conv] to [e] once.
    For multiple applications use [fix conv] (see {!fix}).

    @return a theorem [thm] where [thm] is the proof [ |- e = e']
    and [e'] is the converted version of [e]. If no rewriting took place
    then [thm] is [refl e]. *)

val apply_e : t -> K.ctx -> K.expr -> K.expr * K.thm
(** [apply_e conv ctx e] returns both the theorem [apply conv ctx e],
    and the RHS of the theorem. *)

val fix : t -> t
(** Apply converter repeatedly. *)

val combine : t -> t -> t
(** [combine c1 c2] tries to normalize a term using [c1];
    if [c1] fails it tries [c2]. *)

val combine_l : t list -> t
(** N-ary version of {!combine} *)

val chain_res : K.ctx -> rw_step -> rw_step -> rw_step
(** [chain_res r1 r2] is a lifted version of {!Kernel.Thm.trans} *)
