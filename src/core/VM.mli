
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

(** Chunk of executable bytecode. *)
module Chunk : sig
  type t
  val pp : t Fmt.printer
end

(** Primitive function, implemented in OCaml. *)
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
        name: Name.t;
        ty_chunk: Chunk.t;
      }

    | Define of {
        name: Name.t;
        body_chunk: Chunk.t;
      }

    | Prove of {
        name: Name.t;
        proof: proof;
      }

    | Define_meta of {
        name: string;
        chunk: Chunk.t;
      } (** Define a meta-level chunk *)

    | Eval_meta of {
        (* TODO: some kind of positional name, like a foo.bar.eval.42? *)
        chunk: Chunk.t;
      }

  and proof = private {
    pr_goal_chunk: Chunk.t;
    pr_def: proof_def;
  }
  (** Structured proof *)

  (** Definition of a proof.

      Proofs are structured, they can be either an atomic chunk
      that returns a theorem;
      or a series of steps that can use
      previous steps in a DAG-like fashion.
  *)
  and proof_def = private
    | PR_chunk of {
        thm_chunk: Chunk.t;
      }
    | PR_steps of {
        steps: (string * proof) Vec.t;
        ret: proof;
      }

  val view : t -> view
  (** Examine the stanza *)

  val pp : t Fmt.printer
  (** Pretty print *)
end

(** Scoping environment for the virtual machine.

    This maps local names in scope to symbolic references.
*)
module Scoping_env : sig
  type t
  (** A persistent env *)

  val empty : t

  val pp : t Fmt.printer

  val add : string -> Sym_ptr.t -> t -> t

  val find : string -> t -> Sym_ptr.t option

  val iter : t -> (string * Sym_ptr.t) Iter.t
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

(** Evaluation graph, holding the environment for the virtual machine.

    The VM executes instructions in an environment that contains both
    logical values (expressions, theorems, etc.) and other non-logical
    values (integers, booleans, arrays, etc.).
*)
module Eval_graph : sig
  type t

  val create : unit -> t

    (* TODO

  val add : t -> string -> Value.t -> unit

  val get_stanza : t -> string -> Stanza.t option

  val get : t -> string -> Value.t option

  val get_exn : t -> string -> Value.t

  val iter : t -> Stanza.t Iter.t
       *)
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

val set_debug_hook : t -> (t -> Instr.t -> unit) -> unit
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

val eval_stanza :
  t -> Stanza.t ->
  eg:Eval_graph.t ->
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
