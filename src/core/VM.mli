
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

type vm
type thunk

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

(** Instructions for the VM *)
module Instr : sig
  type t = thunk VM_instr_.t
  include Sigs.PP with type t := t
end

(** Chunk of executable bytecode. *)
module Chunk : sig
  type t
  include PP with type t := t
end

(** Primitive function, implemented in OCaml. *)
module Primitive : sig
  type t
  include PP with type t := t
  val name : t -> string

  (** Make a new primitive. *)
  val make :
    name:string ->
    eval:(vm -> unit) ->
    unit -> t
end

(** Thunks.

    A thunk is a delayed/lazy computation of some {!Chunk.t}. *)
module Thunk : sig
  type t
  include PP with type t := t
end

(** Low level proof/meta stanzas.

    These stanzas provide the basic building blocks for interacting with
    all of Trustee's kernel. A low level proof file is composed of many of
    these stanzas.

    Stanzas rely on VM chunks to define and manipulate logic objects (expressions,
    theorems, substitutions, etc.); however, chunks cannot perform side effects,
    only take and return values, which are then injected into the global
    environment by their containing stanzas.

    In that way, a proof file is, at a high level, declarative. Just looking
    at the stanzas is enough to see what is defined or proved, and where it is.
    Evaluating chunks only has local impact.
*)
module Stanza : sig
  type t
  (** A single stanza *)

  type view = private
    | Declare of {
        name: string;
        ty: Thunk.t;
      }

    | Define of {
        name: string;
        body: Thunk.t;
      }

    | Prove of {
        name: string;
        deps: (string * [`Eager | `Lazy] * string) list;
        goal: Thunk.t; (* sequent *)
        proof: Thunk.t; (* thm *)
      }
      (** Proof a goal using a chunk and some dependencies.
          Dependencies are previous "Prove" steps and each dependency
          [local, kind, name] can be either:

          - {b eager}, in which case we have to prove the step [name]
            and we bind the [local] name to the {b theorem} proved
            at [name]; or:
          - {b lazy}, in which case we just compute the goal of the
            step [name] and we bind [local] to the {b box} of that goal.
            A later step will have to resolve the result with the actual
            boxed proof of the step at [name].
        *)

    | Define_meta of {
        name: string;
        value: Thunk.t;
      } (** Define a meta-level chunk *)

    | Eval_meta of {
        value: Thunk.t;
      }

  val view : t -> view
  (** Examine the stanza *)

  val pp : t Fmt.printer
  (** Pretty print *)
end

(** Scoping environment for the virtual machine.

    This environment contains local names, and is required for parsing.
*)
module Scoping_env : sig
  type t
  (** A persistent env *)

  val empty : t

  val pp : t Fmt.printer
end

(** Basic syntax.

    This syntax is, for now, only intended for testing and possibly as
    an internal compilation target. *)
module Parser : sig
  type t

  val create :
    ?prims:Primitive.t Str_map.t ->
    string -> t
  (** [create ?prims str] creates a parser that will parse [str],
      using [prims] as the additional primitives *)

  val needs_more : string -> bool

  val parse_chunk : t -> env:Scoping_env.t -> (Chunk.t, Error.t) result

  val parse_stanzas :
    t -> env:Scoping_env.t ->
    Scoping_env.t * (Stanza.t Vec.t, Error.t) result
end

type t = vm
(** Virtual machine *)

val create :
  ctx:K.Ctx.t ->
  unit -> t
(** Create a new VM.
    @param ctx the logical context to use to create expressions and
    theorems
    @param env current environment for values in scope.
*)

type debug_hook = t -> Instr.t -> unit

val set_debug_hook : t -> debug_hook -> unit
(** Set a debug hook that is called before each instruction *)

val clear_debug_hook : t -> unit
(** Remove debug hook *)

val reset : t -> unit

val push : t -> Value.t -> unit

val pop : t -> Value.t option

val pop_exn : t -> Value.t

val run :
  t -> Chunk.t ->
  unit

val eval_thunk :
  ?debug_hook:debug_hook ->
  K.Ctx.t ->
  Thunk.t ->
  (Value.t list, Error.t) result
(** Evaluate a thunk (and possibly its dependencies, recursively) *)

val eval_thunk1 :
  ?debug_hook:debug_hook ->
  K.Ctx.t ->
  Thunk.t ->
  (Value.t, Error.t) result

val eval_stanza :
  ?debug_hook:debug_hook ->
  K.Ctx.t -> Stanza.t ->
  unit

val dump : t Fmt.printer
(** Debug printer for the VM.
    Output is not specified, and not guaranteed to be stable. *)

val parse_chunk_string :
  ?prims:Primitive.t Str_map.t ->
  Scoping_env.t -> string -> (Chunk.t, Error.t) result

val parse_chunk_string_exn :
  ?prims:Primitive.t Str_map.t ->
  Scoping_env.t -> string -> Chunk.t

val parse_stanza_string :
  ?prims:Primitive.t Str_map.t ->
  Scoping_env.t -> string -> Scoping_env.t * (Stanza.t, Error.t) result

val parse_stanza_string_exn :
  ?prims:Primitive.t Str_map.t ->
  Scoping_env.t -> string -> Scoping_env.t * Stanza.t
