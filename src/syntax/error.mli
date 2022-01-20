
(** Main error type *)

include Trustee_core.Error.S with type loc = Loc.ctx * Loc.t

val of_kernel_err : Trustee_core.Error.t -> t
