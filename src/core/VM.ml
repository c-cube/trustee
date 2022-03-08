
open Sigs
module K = Kernel
module Str_map = CCMap.Make(String)

type 'a vec = 'a Vec.t

(* all types *)
module Types_ = struct
  type vm = {
    stack: value Vec.t;
    (** Operand stack. *)

    call: chunk Vec.t;
    (** Call stack, containing chunks being executed. The top
        of the stack is the currently running chunk. *)

    mutable ip: int;

    return_stack : int Vec.t;
    (** Value of [ip] for chunks lower in the stack.
        [size return_stack = size call-1] *)

    call_slot_start : int Vec.t;
    (** maps [i] to the beginning of the slice of [slots]
        for frame [i]. The length of the slice is computed
        from [call[i].c_n_slots]. *)

    slots: value Vec.t;
    (** Stack of slots for local register manipulation *)

    env: env Vec.t;
    (** Stack of environments. Lookup walks down the stack, but modification is
        only done on top one. *)
  }

  and value =
    | Nil
    | Bool of bool
    | Int of int
    | String of string
    | Array of value vec
    | Expr of K.Expr.t
    | Thm of K.Thm.t
    | Var of K.Var.t
    | Subst of K.Subst.t
    | Theory of K.Theory.t
    | Chunk of chunk

  (* list of instructions; the atomic block of code *)
  and chunk = {
    c_instrs: instr Vec.t;
    (** Instructions *)

    c_n_slots: int;
    (** Number of slots to allocate for this chunk *)

    c_locals: value Vec.t;
    (** Local values, used by some instructions *)
  }

  (* instruction *)
  and instr = {
    i_exec: vm -> unit;
    i_name: string;
    i_operands: unit -> value array;
  }

  and env = {
    env: value Str_map.t;
  } [@@unboxed]

  let pp_vec ppx out v =
    Fmt.fprintf out "[@[%a@]]" (pp_iter ~sep:", " ppx) (Vec.to_iter v)
  let pp_veci ppx out v =
    Fmt.fprintf out "[@[%a@]]" (pp_iter ~sep:", " ppx)
      (Vec.to_iter v |> Iter.pair_with_idx)

  let rec pp_value out = function
    | Nil -> Fmt.string out "nil"
    | Bool x -> Fmt.bool out x
    | Int x -> Fmt.int out x
    | String x -> Fmt.fprintf out "%S" x
    | Array x -> pp_vec pp_value out x
    | Expr x -> K.Expr.pp out x
    | Thm x -> K.Thm.pp out x
    | Var x -> K.Var.pp out x
    | Subst x -> K.Subst.pp out x
    | Theory x -> K.Theory.pp out x
    | Chunk c -> pp_chunk out c

  and pp_chunk out (self:chunk) : unit =
    let ppi ppx out (i,x) = Fmt.fprintf out "%-8d %a" i ppx x in
    Fmt.fprintf out "@[<v2>chunk[%d] {@ %a@ :locals@ %a@;<1 -2>}@]"
      self.c_n_slots
      (pp_veci @@ ppi pp_instr) self.c_instrs
      (pp_veci @@ ppi pp_value) self.c_locals

  and pp_instr out (self:instr) : unit =
    let ops = self.i_operands() in
    if Array.length ops = 0 then Fmt.string out self.i_name
    else (
      Fmt.fprintf out "(@[%s" self.i_name;
      Array.iter (fun o -> Fmt.fprintf out "@ %a" pp_value o) ops;
      Fmt.fprintf out "@])";
    )

end

module Value = struct
  open Types_
  type t = value

  let nil : t = Nil
  let bool b : t = Bool b
  let int (x:int) : t = Int x
  let string (x:string) : t = String x
  let array (x:t vec) : t = Array x
  let expr (x:K.Expr.t) : t = Expr x
  let thm (x:K.Thm.t) : t = Thm x
  let var (x:K.Var.t) : t = Var x
  let subst (x:K.Subst.t) : t = Subst x
  let theory (x:K.Theory.t) : t = Theory x

  let pp = pp_value

  let rec equal a b = match a, b with
    | Nil, Nil -> true
    | Bool b1, Bool b2 -> b1=b2
    | Int i, Int j -> i=j
    | String s1, String s2 -> s1=s2
    | Array v1, Array v2 -> Vec.equal equal v1 v2
    | Expr e1, Expr e2 -> K.Expr.equal e1 e2
    | Thm th1, Thm th2 -> K.Thm.equal th1 th2
    | Var v1, Var v2 -> K.Var.equal v1 v2
    | Subst s1, Subst s2 -> K.Subst.equal s1 s2
    | Theory th1, Theory th2 -> th1 == th2
    | Chunk c1, Chunk c2 -> c1 == c2
    | (Bool _ | Int _ | String _ | Array _
      | Expr _ | Thm _ | Var _ | Subst _ |
       Theory _ | Nil | Chunk _), _ -> false
end

module Env = struct
  open Types_
  type t = env

  let empty : t = {env=Str_map.empty}

  let pp out self =
    let pp_pair out (s,v) =
      Fmt.fprintf out "@[%s := %a@]" s Value.pp v in
    Fmt.fprintf out "@[<1>env {@ %a@ @;<0 -1>}@]"
      (pp_iter ~sep:";" pp_pair) (Str_map.to_iter self.env)

  let[@inline] add s v self : t = {env=Str_map.add s v self.env}
  let[@inline] find s self = Str_map.find_opt s self.env
  let[@inline] iter self = Str_map.to_iter self.env
end

module Chunk = struct
  open Types_
  type t = chunk
  let pp = pp_chunk
end

(* internal handling of the VM *)
module VM_ = struct
  open Types_
  type t = vm

  let create() : t = {
    stack=Vec.make 128 Value.nil;
    call=Vec.create();
    ip=0;
    return_stack=Vec.create();
    call_slot_start=Vec.create();
    slots=Vec.make 32 Value.nil;
    env=Vec.create();
  }

  let[@inline] push (self:t) v = Vec.push self.stack v
  let[@inline] pop (self:t) = Vec.pop self.stack

  (* reset state entirely *)
  let reset (self:t) : unit =
    let { stack; call; ip=_; return_stack; call_slot_start; slots; env } = self in
    self.ip <- 0;
    Vec.clear stack;
    Vec.clear return_stack;
    Vec.clear call_slot_start;
    Vec.clear call;
    Vec.clear slots;
    Vec.clear env;
    ()

  let enter_chunk (self:t) (c:chunk) =
    if not (Vec.is_empty self.call) then (
      Vec.push self.return_stack self.ip; (* when we exit *)
    );
    self.ip <- 0;
    Vec.push self.call c;
    Vec.push self.call_slot_start (Vec.size self.slots);
    for _j = 1 to c.c_n_slots do
      Vec.push self.slots Value.nil
    done

  (* FIXME: maybe, like [ip], a toplevel [chunk] pointer
     (init to a dummy chunk with nothing in it)?
     this should make access to current chunk much faster
  *)

  (* TODO: debug function, to print current state of VM
     including stacks *)

  let run (self:t) =
    let continue = ref true in
    while !continue do

      (* TODO:
        - find current chunks
      *)
      assert false

    done
end

(* instructions *)
module Instr = struct
  open Types_
  type t = instr
  let pp = pp_instr

  (* TODO: a ton of instructions *)

end

type t = Types_.vm

let create ?(env=Env.empty) () : t =
  let vm = VM_.create() in
  Vec.push vm.env env;
  vm

let get_env (self:t) =
  Vec.last_exn self.env

let reset = VM_.reset
let push = VM_.push
let pop = VM_.pop
let run self c =
  VM_.enter_chunk self c;
  VM_.run self

