
open Common_
module VM = Trustee_core.VM
module A = Ast

type stanza = VM.Stanza.t
type thunk = VM.Thunk.t

module Env = struct
  module M = Str_map

  type t = {
    ths: thunk M.t;
  }

  let empty : t = {ths=M.empty}

  let add_stanza (st:VM.Stanza.t) self : t =
    match VM.Stanza.view st with
    | VM.Stanza.Declare _
    | VM.Stanza.Define _
    | VM.Stanza.Define_meta _
    | VM.Stanza.Prove _
    | VM.Stanza.Eval_meta _
      -> assert false (* TODO *)
        (*
    {ths=M.add s th self.ths}
           *)

  let pp out self =
    let pp_kv out (k,v) = Fmt.fprintf out "@[%s := %a@]" k VM.Thunk.pp v in
    Fmt.fprintf out "@[<2>env{@ %a@;<1 -2>}@]"
      (pp_iter pp_kv) (M.to_iter self.ths)
end

module Compile_ = struct
  module I = VM.Instr
  module CB = VM.Chunk_builder


  let top (env:Env.t) (p:A.statement) : Env.t * _ list =
    assert false
end

let compile = Compile_.top


let compile_l = CCList.fold_flat_map compile
