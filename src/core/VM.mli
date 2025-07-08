(** Virtual machine.

    We embed a little virtual machine, with instructions manipulating the stack
    and some locally allocated registers (slots in a stack frame, really).

    This machine is not typed, but must be a good target for a typed
    meta-language. It should also allow for more efficient implementations in
    other languages (rust, C, etc.) *)

open Sigs
module K = Kernel

type 'a vec
type vm
type thunk
type chunk
type primitive

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
  val prim : primitive -> t
  val chunk : chunk -> t
  val thunk : thunk -> t

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
  type t = VM_instr_.t

  include module type of VM_instr_.Build
  include Sigs.PP with type t := t
end

(** Chunk of executable bytecode. *)
module Chunk : sig
  type t = chunk

  val strip_comments : t -> unit

  include PP with type t := t

  val debug : t Fmt.printer
end

(** Primitive operation.

    A primitive is a function implemented in OCaml (or the host language, in
    general), that operates over the VM, and can perform computations more
    efficiently. It should be referentially transparent.

    A good use of primitives is to implement logical algorithms such as
    unification, rewriting, congruence closure, etc. and expose them as fast
    primitive operations to help user programs reason. *)
module Primitive : sig
  type t = primitive

  include PP with type t := t

  val name : t -> string

  val make : name:string -> eval:(vm -> unit) -> unit -> t
  (** Make a new primitive. *)
end

(** Thunks.

    A thunk is a delayed/lazy computation of some {!Chunk.t}. *)
module Thunk : sig
  type t = thunk

  include PP with type t := t

  val debug : t Fmt.printer

  val make : chunk -> t
  (** Build a thunk that will evaluate this chunk. *)
end

(** Low level proof/meta stanzas.

    These stanzas provide the basic building blocks for interacting with all of
    Trustee's kernel. A low level proof file is composed of many of these
    stanzas.

    Stanzas rely on VM chunks to define and manipulate logic objects
    (expressions, theorems, substitutions, etc.); however, chunks cannot perform
    side effects, only take and return values, which are then injected into the
    global environment by their containing stanzas.

    In that way, a proof file is, at a high level, declarative. Just looking at
    the stanzas is enough to see what is defined or proved, and where it is.
    Evaluating chunks only has local impact. *)
module Stanza : sig
  type t
  (** A single stanza *)

  type view =
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
        deps: (string * [ `Eager | `Lazy ] * string) list;
        goal: Thunk.t; (* sequent *)
        proof: Thunk.t; (* thm *)
      }
        (** Proof a goal using a chunk and some dependencies. Dependencies are
            previous "Prove" steps and each dependency [local, kind, name] can
            be either:

            - {b eager}, in which case we have to prove the step [name] and we
              bind the [local] name to the {b theorem} proved at [name]; or:
            - {b lazy}, in which case we just compute the goal of the step
              [name] and we bind [local] to the {b box} of that goal. A later
              step will have to resolve the result with the actual boxed proof
              of the step at [name]. *)
    | Define_thunk of {
        name: string;
        value: Thunk.t;
      }  (** Define a meta-level chunk *)
    | Define_chunk of {
        name: string;
        value: Chunk.t;
      }  (** Define a meta-level chunk *)
    | Eval of { value: Thunk.t }

  val make : id:Sym_ptr.t -> view -> t

  val view : t -> view
  (** Examine the stanza *)

  val pp : t Fmt.printer
  (** Pretty print *)

  val debug : t Fmt.printer
  (** Pretty printer for debug *)
end

(** Object used to build chunks incrementally. *)
module Chunk_builder : sig
  type t

  val create : ?allow_comments:bool -> n_args:int -> n_ret:int -> unit -> t
  (** Create a new chunk builder.
      @param n_args number of arguments the chunk takes
      @param n_ret number of values returned by the chunk *)

  val reset : t -> unit

  val to_chunk : t -> Chunk.t
  (** Obtain the chunk that we just built *)

  val add_local : t -> Value.t -> int
  (** Add a local value to this chunk, returning its index. *)

  val push_i : t -> Instr.t -> unit
  (** Push an instruction *)

  val push_comment : t -> string -> unit
  (** Add short comment on the current instruction *)

  val cur_pos : t -> int
  (** current position in the list of instructions. This can be useful for
      emitting a jump to this instruction later on. *)

  val set_i : t -> int -> Instr.t -> unit
  (** [set_i builder off instr] sets the existing instruction at offset [off] to
      [instr]. This is useful to emit a forward jump once the offset it jumps
      to, is known. *)
end

type t = vm
(** Virtual machine *)

val create : ctx:K.Ctx.t -> unit -> t
(** Create a new VM.
    @param ctx the logical context to use to create expressions and theorems
    @param env current environment for values in scope. *)

type debug_hook = t -> Instr.t -> unit

val set_debug_hook : t -> debug_hook -> unit
(** Set a debug hook that is called before each instruction *)

val clear_debug_hook : t -> unit
(** Remove debug hook *)

val reset : t -> unit
val push : t -> Value.t -> unit
val pop : t -> Value.t option
val pop_exn : t -> Value.t
val run : t -> Chunk.t -> unit

val eval_thunk :
  ?debug_hook:debug_hook -> K.Ctx.t -> Thunk.t -> (Value.t list, Error.t) result
(** Evaluate a thunk (and possibly its dependencies, recursively) *)

val eval_thunk1 :
  ?debug_hook:debug_hook -> K.Ctx.t -> Thunk.t -> (Value.t, Error.t) result

module Eval_effect : sig
  type t =
    | Eff_declare of string * K.ty
    | Eff_define of string * K.Expr.t
    | Eff_print_val of Value.t
    | Eff_prove of string * K.Sequent.t * K.Thm.t Error.or_error
    | Eff_define_thunk of string * thunk
    | Eff_define_chunk of string * chunk
    | Eff_print_error of Error.t

  val pp : t Fmt.printer
end

val eval_stanza :
  ?debug_hook:debug_hook -> K.Ctx.t -> Stanza.t -> Eval_effect.t list

val eval_stanza_pp : ?debug_hook:debug_hook -> K.Ctx.t -> Stanza.t -> unit

val dump : t Fmt.printer
(** Debug printer for the VM. Output is not specified, and not guaranteed to be
    stable. *)
