
module K = Trustee_core.Kernel

type value = Value.t

type t = {
  ctx: K.ctx;
  mutable env: Env.t;
}

let create ctx : t =
  { ctx; env=Env.empty; }
