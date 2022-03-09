
open Sigs
module K = Kernel
module Str_map = CCMap.Make(String)

type 'a vec = 'a Vec.t

(* all types *)
module Types_ = struct
  type vm = {
    stack: value Vec.t;
    (** Operand stack. *)

    mutable chunk : chunk; (** current chunk *)
    mutable ip: int; (** current offset in chunk *)

    return_stack_chunk : chunk Vec.t;
    (** Value of [chunk] for chunks lower in the call stack. *)

    return_stack_ip : int Vec.t;
    (** Value of [ip] for chunks lower in the call stack.
        [size return_stack_chunk = size return_stack_ip] *)

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
    c_instrs: instr array;
    (** Instructions *)

    c_n_slots: int;
    (** Number of slots to allocate for this chunk *)

    c_locals: value array;
    (** Local values, used by some instructions *)
  }

  (* instruction *)
  and instr = {
    i_exec: vm -> unit;
    i_name: string;
    i_doc: string;
    i_operands: unit -> value array;
  }

  and env = {
    env: value Str_map.t;
  } [@@unboxed]

  let pp_vec ppx out v =
    Fmt.fprintf out "[@[%a@]]" (pp_iter ~sep:", " ppx) (Vec.to_iter v)
  let pp_arri ppx out a =
    Fmt.fprintf out "[@[%a@]]" (pp_iter ~sep:", " ppx)
      (Iter.of_array_i a)

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
      (pp_arri @@ ppi pp_instr) self.c_instrs
      (pp_arri @@ ppi pp_value) self.c_locals

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
  let chunk c : t = Chunk c

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

  (* empty chunk, does nothing *)
  let dummy : t = {
    c_n_slots=0;
    c_locals=[||];
    c_instrs=[||];
  }
end

(* internal handling of the VM *)
module VM_ = struct
  open Types_
  type t = vm

  (* exception used in instructions to stop execution right now.
     This doesn't unwind the stack.

     Caution: this must only be raised from within the VM, i.e. within
     an instruction. *)
  exception Stop_exec

  let create() : t = {
    stack=Vec.make 128 Value.nil;
    ip=0;
    chunk=Chunk.dummy;
    return_stack_chunk=Vec.create();
    return_stack_ip=Vec.create();
    call_slot_start=Vec.create();
    slots=Vec.make 32 Value.nil;
    env=Vec.create();
  }

  let[@inline] push_val (self:t) v = Vec.push self.stack v
  let[@inline] pop_val (self:t) = Vec.pop self.stack
  let pop_val_exn (self:t) : Value.t =
    if Vec.is_empty self.stack then (
      Error.fail"vm.pop: operand stack is empty";
    );
    Vec.pop_exn self.stack

  let swap_val (self:t) =
    if Vec.size self.stack < 2 then (
      Error.fail"vm.swap: operand stack too small";
    );
    let v1 = Vec.pop_exn self.stack in
    let v2 = Vec.pop_exn self.stack in
    Vec.push self.stack v1;
    Vec.push self.stack v2

  let extract_ (self:t) i =
    if i >= Vec.size self.stack then (
      Error.fail"vm.extract: operand stack too small";
    );
    let v = Vec.get self.stack (Vec.size self.stack - i - 1) in
    Vec.push self.stack v

  (* reset state entirely *)
  let reset (self:t) : unit =
    let { stack;
          ip=_; chunk=_;
          return_stack_chunk; return_stack_ip;
          call_slot_start; slots; env } = self in
    self.ip <- 0;
    self.chunk <- Chunk.dummy;
    Vec.clear stack;
    Vec.clear return_stack_chunk;
    Vec.clear return_stack_ip;
    Vec.clear call_slot_start;
    Vec.clear slots;
    Vec.clear env;
    ()

  let enter_chunk (self:t) (c:chunk) : unit =
    if self.chunk != Chunk.dummy then (
      (* when we exit, restore current state *)
      Vec.push self.return_stack_chunk self.chunk;
      Vec.push self.return_stack_ip self.ip;
    );
    self.ip <- 0;
    self.chunk <- c;
    (* allocate slots for [c] *)
    Vec.push self.call_slot_start (Vec.size self.slots);
    for _j = 1 to c.c_n_slots do
      Vec.push self.slots Value.nil
    done

  let pop_chunk (self:t) : unit =
    if Vec.is_empty self.return_stack_ip then (
      if self.chunk == Chunk.dummy then (
        Error.fail "vm.pop_chunk: empty call stack"
      );
      self.chunk <- Chunk.dummy;
      self.ip <- 0;
    ) else (
      self.chunk <- Vec.pop_exn self.return_stack_chunk;
      self.ip <- Vec.pop_exn self.return_stack_ip;
    )

  let get_slot (self:t) (i:int) : Value.t =
    let n = self.chunk.c_n_slots in
    if i >= n then Error.failf (fun k->k"vm.get_slot %d: chunk only has %d slots" i n);
    let off = Vec.last_exn self.call_slot_start in
    Vec.get self.slots (off + i)

  let set_slot (self:t) (i:int) v : unit =
    let n = self.chunk.c_n_slots in
    if i >= n then Error.failf (fun k->k"vm.set_slot %d: chunk only has %d slots" i n);
    let off = Vec.last_exn self.call_slot_start in
    Vec.set self.slots (off + i) v

  (* TODO: debug function, to print current state of VM
     including stacks *)

  let run (self:t) =
    let continue = ref true in
    try
      while !continue do

        let ip = self.ip in
        assert (ip >= 0);
        let c = self.chunk in

        if ip < Array.length c.c_instrs then (
          (* execute current instruction *)
          let instr = Array.unsafe_get c.c_instrs ip in
          self.ip <- self.ip + 1; (* preemptively advance by 1 *)
          instr.i_exec self;

        ) else (
          (* done with chunk *)
          if Vec.is_empty self.return_stack_ip then (
            continue := false; (* all done *)
          ) else (
            (* return to caller *)
            self.ip <- Vec.pop_exn self.return_stack_ip;
            self.chunk <- Vec.pop_exn self.return_stack_chunk;
          )
        )
      done
    with Stop_exec ->
      ()
end

(* instructions *)
module Instr = struct
  open Types_
  type t = instr
  let pp = pp_instr

  let op0_ () = [||]

  let[@inline] make_ ~name ~doc ~ops exec : t =
    { i_name=name; i_operands=ops; i_doc=doc; i_exec=exec; }

  (** Call the given chunk *)
  let call (c:chunk) : t =
    make_ ~name:"call" ~ops:op0_
      ~doc:"(chunk -- ) Pop and call the chunk that is on top of the stack"
      (fun vm ->
         let c = VM_.pop_val_exn vm in
         match c with
         | Chunk c -> VM_.enter_chunk vm c
         | _ -> Error.failf (fun k->k"call: expected a chunk,@ got %a" Value.pp c)
      )

  let ret : t =
    make_ ~name:"ret" ~ops:op0_ ~doc:"return from current chunk"
      (fun vm -> VM_.pop_chunk vm)

  let drop : t =
    make_ ~name:"drop" ~ops:op0_
      ~doc:"(a -- ) drop value on top of stack, discarding it"
      (fun vm -> ignore (VM_.pop_val_exn vm : Value.t))

  let exch : t =
    make_ ~name:"exch" ~ops:op0_
      ~doc:"(a b -- b a) exchange the two top values of the stack"
      (fun vm -> VM_.swap_val vm)

  let extract i : t =
    make_ ~name:"exch"
      ~doc:"(vs -- vs vs[-i]) extract i-th value, where 0 is top of the stack"
      ~ops:(fun () -> [|Value.int i|])
      (fun vm -> VM_.extract_ vm i)

  let set_reg i : t =
    make_ ~name:"set_reg"
      ~doc:"(x -- ) Pop value and move it to register i"
      ~ops:(fun () -> [|Value.int i|])
      (fun vm ->
         let v = VM_.pop_val_exn vm in
         VM_.set_slot vm i v)

  let get_reg i : t =
    make_ ~name:"get_reg"
      ~doc:"( -- x) Get value from register i and push it onto stack"
      ~ops:(fun () -> [|Value.int i|])
      (fun vm ->
         let v = VM_.get_slot vm i in
         VM_.push_val vm v)

  let get_local i : t =
    make_ ~name:"get_local"
      ~ops:(fun () -> [|Value.int i|])
      ~doc:"( -- x) Get i-th local value of current chunk and push it onto stack"
      (fun vm ->
         let c = vm.chunk in
         if i < Array.length c.c_locals then (
           let v = Array.get c.c_locals i in
           VM_.push_val vm v
         ) else Error.fail"vm.get_local: invalid index"
      )

  let int (i:int) : t =
    let v = Value.int i in
    make_ ~name:"int" ~ops:(fun () -> [|v|])
      ~doc:"Push an integer on the stack"
      (fun vm -> VM_.push_val vm v)

  let bool b : t =
    let v = Value.bool b in
    make_ ~name:"bool" ~ops:(fun () -> [|v|])
      ~doc:"Push a boolean on the stack"
      (fun vm -> VM_.push_val vm v)

  let nil : t =
    make_ ~name:"bool" ~ops:op0_
      ~doc:"Push nil on the stack"
      (fun vm -> VM_.push_val vm Value.nil)

  let not : t =
    make_ ~name:"not " ~ops:op0_
      ~doc:"(a -- not(a)) Negate top value"
      (fun vm ->
         let a = VM_.pop_val_exn vm in
         match a with
         | Bool b -> VM_.push_val vm (Value.bool (not b))
         | _ -> Error.fail "vm.not: type error"
      )

  let add1 : t =
    make_ ~name:"add1" ~ops:op0_
      ~doc:"(a -- a+1) Increment top of stack"
      (fun vm ->
         let a = VM_.pop_val_exn vm in
         match a with
         | Int a -> VM_.push_val vm (Value.int (a+1))
         | _ -> Error.fail "vm.add1: type error"
      )

  let add : t =
    make_ ~name:"add" ~ops:op0_
      ~doc:"(a b -- a+b) Pop two values, adds them"
      (fun vm ->
         let b = VM_.pop_val_exn vm in
         let a = VM_.pop_val_exn vm in
         match a, b with
         | Int a, Int b ->
           VM_.push_val vm (Value.int (a+b))
         | _ -> Error.fail "vm.add: type error"
      )

  let sub : t =
    make_ ~name:"sub" ~ops:op0_
      ~doc:"(a b -- a-b) Pop two values, subtract them"
      (fun vm ->
         let b = VM_.pop_val_exn vm in
         let a = VM_.pop_val_exn vm in
         match a, b with
         | Int a, Int b ->
           VM_.push_val vm (Value.int (a-b))
         | _ -> Error.fail "vm.sub: type error"
      )

  let jeq (ip:int) : t =
    make_ ~name:"jeq" ~ops:(fun () -> [| Value.int ip |])
      ~doc:"(a b -- ) Pop two values; if a = b then set IP"
      (fun vm ->
         let b = VM_.pop_val_exn vm in
         let a = VM_.pop_val_exn vm in
         if Value.equal a b then vm.ip <- ip
      )

  let jlt (ip:int) : t =
    make_ ~name:"jlt" ~ops:(fun () -> [| Value.int ip |])
      ~doc:"(a b -- ) Pop two integer values; if a < b then set IP"
      (fun vm ->
         let b = VM_.pop_val_exn vm in
         let a = VM_.pop_val_exn vm in
         match a, b with
         | Int a, Int b -> if a < b then vm.ip <- ip;
         | _ -> Error.fail "vm.jlt: type error"
      )

  let jleq (ip:int) : t =
    make_ ~name:"jleq" ~ops:(fun () -> [| Value.int ip |])
      ~doc:"(a b -- ) Pop two integer values; if a <= b then set IP"
      (fun vm ->
         let b = VM_.pop_val_exn vm in
         let a = VM_.pop_val_exn vm in
         match a, b with
         | Int a, Int b -> if a <= b then vm.ip <- ip;
         | _ -> Error.fail "vm.jleq: type error"
      )

  let jump (ip:int) : t =
    make_ ~name:"jump" ~ops:(fun () -> [| Value.int ip |])
      ~doc:"( -- ) Set IP unconditionally"
      (fun vm -> vm.ip <- ip)

  let nop : t =
    make_ ~name:"nop" ~ops:op0_
      ~doc:"( -- ) Do nothing"
      (fun _vm -> ())

end

type t = Types_.vm

let create ?(env=Env.empty) () : t =
  let vm = VM_.create() in
  Vec.push vm.env env;
  vm

let get_env (self:t) =
  Vec.last_exn self.env

let reset = VM_.reset
let push = VM_.push_val
let pop = VM_.pop_val
let run self c =
  VM_.enter_chunk self c;
  VM_.run self

