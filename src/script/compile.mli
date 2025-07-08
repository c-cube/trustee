module A = Ast
module VM = Trustee_core.VM

type stanza = VM.Stanza.t
type thunk = VM.Thunk.t

module Env : sig
  type t

  val empty : t
  val add_stanza : t -> stanza -> t
  val pp : t Fmt.printer
end

val compile : Env.t -> A.statement -> Env.t * stanza list
val compile_l : Env.t -> A.statement list -> Env.t * stanza list
