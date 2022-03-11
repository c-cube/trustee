
(** Virtual machine.

    We embed a little virtual machine, with instructions manipulating
    the stack and some locally allocated registers (slots in a stack frame,
    really).

    This machine is not typed, but must be a good target for a typed
    meta-language. It should also allow for more efficient implementations
    in other languages (rust, C, etc.)
*)

open Sigs
module K = Kernel

type 'a vec

module Instr = VM_instr

(** Values manipulated by the VM. *)
module Value : sig
  type t

  val nil : t
  val bool : bool -> t
  val int : int -> t
  val string : string -> t
  val array : t vec -> t
  val expr : K.Expr.t -> t
  val thm : K.Thm.t -> t
  val var : K.Var.t -> t
  val subst : K.Subst.t -> t
  val theory : K.Theory.t -> t

  (* TODO: custom values? *)

  val equal : t -> t -> bool
  val pp : t Fmt.printer
end

(** Environment for the virtual machine.

    The VM executes instructions in an environment that contains both
    logical values (expressions, theorems, etc.) and other non-logical
    values (integers, booleans, arrays, etc.). These environments are
    persistent and can be stacked (so that modifications are local only).
*)
module Env : sig

  type t
  (** A persistent env *)

  val empty : t

  val pp : t Fmt.printer

  val add : string -> Value.t -> t -> t

  val find : string -> t -> Value.t option

  val iter : t -> (string * Value.t) Iter.t
end

(** Chunk of executable bytecode *)
module Chunk : sig
  type t
  val pp : t Fmt.printer
end

type t
(** Virtual machine *)

val create : ?env:Env.t -> unit -> t

val get_env : t -> Env.t

val reset : t -> unit

val push : t -> Value.t -> unit

val pop : t -> Value.t option

val run : t -> Chunk.t -> unit

