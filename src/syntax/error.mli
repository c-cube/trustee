
(** Main error type.

    This error type has an optional location, unlike {!Trustee_core.Error}.
    This allows for better error reporting. *)

include Trustee_core.Error.S with type loc = Loc.t

val of_kernel_err : Trustee_core.Error.t -> t
