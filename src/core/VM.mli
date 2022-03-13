
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

type vm

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
  val show : t -> string

  type 'a conv_to = t -> 'a option
  type 'a conv_to_exn = t -> 'a

  val to_str : string conv_to
  val to_bool : bool conv_to
  val to_int : int conv_to

  val to_str_exn : string conv_to_exn
  val to_bool_exn : bool conv_to_exn
  val to_int_exn : int conv_to_exn
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

(** Chunk of executable bytecode *)
module Primitive : sig
  type t
  val pp : t Fmt.printer
  val name : t -> string

  (** Make a new primitive. *)
  val make :
    name:string ->
    eval:(vm -> unit) ->
    unit -> t
end

(** Basic syntax.

    This syntax is, for now, only intended for testing and possibly as
    an internal compilation target. *)
module Parser : sig
  type t

  val create :
    ?prims:Primitive.t Str_map.t ->
    string -> t

  val needs_more : string -> bool

  val parse : t -> (Chunk.t, Error.t) result
end

type t = vm
(** Virtual machine *)

val create : ?env:Env.t -> unit -> t

val set_debug_hook : t -> (t -> Instr.t -> unit) -> unit
(** Set a debug hook that is called before each instruction *)

val clear_debug_hook : t -> unit
(** Remove debug hook *)

val get_env : t -> Env.t

val set_env : t -> Env.t -> unit

val reset : t -> unit

val push : t -> Value.t -> unit

val pop : t -> Value.t option

val pop_exn : t -> Value.t

val run : t -> Chunk.t -> unit

val dump : t Fmt.printer

val parse_string :
  ?prims:Primitive.t Str_map.t ->
  string -> (Chunk.t, Error.t) result

val parse_string_exn :
  ?prims:Primitive.t Str_map.t ->
  string -> Chunk.t
