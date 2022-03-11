
open Sigs
module K = Kernel
module Str_map = CCMap.Make(String)

type 'a vec = 'a Vec.t

(* all types *)
module Types_ = struct
  type vm = {
    stack: value Vec.t;
    (** Operand stack. *)

    call_stack : chunk Vec.t;
    (** Chunks currently being evaluated. The active chunk is the one
        on top. *)

    mutable ip: int;
    (** Instruction pointer for topmost chunk in {!call_stack} *)

    call_restore_ip : int Vec.t;
    (** IP for all items in [call_stack] except the last. *)

    call_reg_start : int Vec.t;
    (** maps [i] to the beginning of the slice of [regs]
        for frame [i]. The length of the slice is computed
        from [call[i].c_n_regs] if it's a chunk, and 0
        if it's a primitive. *)

    call_prim: primitive Vec.t;
    (** Primitives currently being evaluated *)

    regs: value Vec.t;
    (** Stack of register value. Each call frame has its own
        local register. *)

    env: env;
    (** Logical environment. The VM cannot modify it. *)
  }

  and call_item =
    | C_chunk of {
        c: chunk;
        mutable ip: int;
        (** Value of [ip] in that chunk *)
      }

    | C_prim of primitive

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
    | Prim of primitive

  (** Primitive implemented in OCaml *)
  and primitive = {
    pr_name: string;
    pr_eval: vm -> unit;
  }

  (* list of instructions; the atomic block of code *)
  and chunk = {
    c_instrs: instr array;
    (** Instructions *)

    c_n_regs: int;
    (** Number of regs to allocate for this chunk *)

    c_locals: value array;
    (** Local values, used by some instructions *)
  }

  and instr = VM_instr.t

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
    | Prim p -> pp_prim out p

  and pp_chunk out (self:chunk) : unit =
    let ppi ppx out (i,x) = Fmt.fprintf out "%-8d %a" i ppx x in
    Fmt.fprintf out "@[<v2>chunk[%d] {@ %a@ :locals@ %a@;<1 -2>}@]"
      self.c_n_regs
      (pp_arri @@ ppi VM_instr.pp) self.c_instrs
      (pp_arri @@ ppi pp_value) self.c_locals

  and pp_prim out (p:primitive) : unit =
    Fmt.string out p.pr_name
end

(** Instructions *)
module Instr = VM_instr

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
    | Prim p1, Prim p2 -> p1.pr_name = p2.pr_name
    | (Bool _ | Int _ | String _ | Array _
      | Expr _ | Thm _ | Var _ | Subst _ |
       Theory _ | Nil | Chunk _ | Prim _), _ -> false
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
    c_n_regs=0;
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

  let create (env:Env.t) : t = {
    stack=Vec.make 128 Value.nil;
    call_stack=Vec.make 12 Chunk.dummy;
    call_restore_ip=Vec.make 12 0;
    call_prim=Vec.create ();
    ip=0;
    call_reg_start=Vec.create();
    regs=Vec.make 32 Value.nil;
    env;
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
    let { stack; call_stack; ip=_; call_prim=_;
          call_restore_ip; call_reg_start; regs; env } = self in
    self.ip <- 0;
    Vec.clear self.call_stack;
    Vec.clear self.call_restore_ip;
    Vec.clear stack;
    Vec.clear call_reg_start;
    Vec.clear self.call_prim;
    Vec.clear regs;
    ()

  let enter_chunk (self:t) (c:chunk) : unit =
    if not (Vec.is_empty self.call_stack) then (
      Vec.push self.call_restore_ip self.ip;
    );
    Vec.push self.call_stack c;
    self.ip <- 0;
    (* allocate regs for [c] *)
    Vec.push self.call_reg_start (Vec.size self.regs);
    for _j = 1 to c.c_n_regs do
      Vec.push self.regs Value.nil
    done

  let pop_chunk (self:t) : unit =
    let _ = Vec.pop_exn self.call_stack in
    if not (Vec.is_empty self.call_restore_ip) then (
      assert (not (Vec.is_empty self.call_stack));
      self.ip <- Vec.pop_exn self.call_restore_ip;
    )

  let eval_prim (self:t) (p:primitive) : unit =
    let len = Vec.size self.call_stack in
    Vec.push self.call_prim p;
    p.pr_eval self;
    let len' = Vec.size self.call_stack in
    if len' <> len then (
      Error.failf (fun k->k"vm.eval-prim: call stack changed (size %d->%d)" len len');
    );
    begin match Vec.pop self.call_prim with
      | Some p' -> assert (p == p');
      | _ ->
        Error.fail "vm.eval-prim: mismatched current primitive"
    end

  let rload (self:t) (i:int) : Value.t =
    let c = Vec.last_exn self.call_stack in
    let n = c.c_n_regs in
    if i >= n then Error.fail"vm.rload: invalid register";
    let off = Vec.last_exn self.call_reg_start in
    Vec.get self.regs (off + i)

  let rstore (self:t) (i:int) v : unit =
    let c = Vec.last_exn self.call_stack in
    let n = c.c_n_regs in
    if i >= n then Error.fail "vm.rstore: not enough registers";
    let off = Vec.last_exn self.call_reg_start in
    Vec.set self.regs (off + i) v

  (* TODO: debug function, to print current state of VM
     including stacks *)

  let run (self:t) =
    let continue = ref true in
    try
      while !continue do
        let ip = self.ip in
        assert (ip >= 0);
        let c = Vec.last_exn self.call_stack in

        if ip >= Array.length c.c_instrs then (
          (* done with chunk *)
          pop_chunk self;
          if Vec.is_empty self.call_stack then (
            continue := false; (* all done *)
          )
        ) else (
          (* execute current instruction in [c] *)
          let instr = Array.unsafe_get c.c_instrs ip in
          self.ip <- self.ip + 1; (* preemptively advance by 1 *)

          match instr with
          | Nop -> ()
          | Ret -> pop_chunk self
          | Drop -> ignore (pop_val_exn self : Value.t)
          | Exch -> swap_val self
          | Extract i -> extract_ self i

          | Int i -> push_val self (Value.int i)
          | Bool b -> push_val self (Value.bool b)
          | Nil -> push_val self Value.nil

          | Call ->
            let c = pop_val_exn self in
            begin match c with
              | Chunk c -> enter_chunk self c
              | Prim p -> eval_prim self p
              | _ -> Error.failf (fun k->k"call: expected a chunk,@ got %a" Value.pp c)
            end;

          | Rstore i ->
            let v = pop_val_exn self in
            rstore self i v

          | Rload i ->
            let v = rload self i in
            push_val self v

          | Lload i ->
            if i < Array.length c.c_locals then (
              let v = Array.get c.c_locals i in
              push_val self v
            ) else Error.fail"vm.lload: invalid index"

          | Not ->
            let a = pop_val_exn self in
            begin match a with
              | Bool b -> push_val self (Value.bool (not b))
              | _ -> Error.fail "self.not: type error"
            end

          | Add ->
            let b = pop_val_exn self in
            let a = pop_val_exn self in
            begin match a, b with
              | Int a, Int b ->
                push_val self (Value.int (a+b))
              | _ -> Error.fail "self.add: type error"
            end

          | Add1 ->
            let a = pop_val_exn self in
            begin match a with
              | Int a -> push_val self (Value.int (a+1))
              | _ -> Error.fail "self.add1: type error"
            end

          | Sub ->
            let b = pop_val_exn self in
            let a = pop_val_exn self in
            begin match a, b with
              | Int a, Int b ->
                push_val self (Value.int (a-b))
              | _ -> Error.fail "self.sub: type error"
            end
          | Sub1 ->
            let a = pop_val_exn self in
            begin match a with
              | Int a -> push_val self (Value.int (a-1))
              | _ -> Error.fail "self.sub1: type error"
            end

          | Jeq ip ->

            let b = pop_val_exn self in
            let a = pop_val_exn self in
            if Value.equal a b then self.ip <- ip


          | Jlt ip ->
            let b = pop_val_exn self in
            let a = pop_val_exn self in
            begin match a, b with
              | Int a, Int b -> if a < b then self.ip <- ip;
              | _ -> Error.fail "self.jlt: type error"
            end

          | Jleq ip ->

            let b = pop_val_exn self in
            let a = pop_val_exn self in
            begin match a, b with
              | Int a, Int b -> if a <= b then self.ip <- ip;
              | _ -> Error.fail "self.jleq: type error"
            end
          | Jmp ip ->
            self.ip <- ip
        )
      done
    with Stop_exec ->
      ()
end

(* TODO: chunk builder, with vecs inside, expose create/reset/add_instr/add_local *)
(* TODO: expose instructions so that ITP can use its own syntax for VM? *)
(* TODO: basic parser + chunk assembler? from Sexp? *)

type t = Types_.vm

let create ?(env=Env.empty) () : t =
  let vm = VM_.create env in
  vm

let get_env (self:t) = self.env

let reset = VM_.reset
let push = VM_.push_val
let pop = VM_.pop_val
let run self c =
  VM_.enter_chunk self c;
  VM_.run self

