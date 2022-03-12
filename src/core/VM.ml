
open Sigs
module K = Kernel

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

    mutable env: env;
    (** Logical environment. The VM itself cannot modify it. *)
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

  let pp_vec ?(sep=", ") ppx out v =
    Fmt.fprintf out "%a" (pp_iter ~sep ppx) (Vec.to_iter v)
  let pp_arri ?(sep=", ") ppx out a =
    Fmt.fprintf out "%a" (pp_iter ~sep ppx)
      (Iter.of_array_i a)

  let rec pp_value ~short out = function
    | Nil -> Fmt.string out "nil"
    | Bool x -> Fmt.bool out x
    | Int x -> Fmt.int out x
    | String x -> Fmt.fprintf out "%S" x
    | Array x ->
      Fmt.fprintf out "[@[%a@]]" (pp_vec ~sep:", " @@ pp_value ~short) x
    | Expr x -> K.Expr.pp out x
    | Thm x -> K.Thm.pp out x
    | Var x -> K.Var.pp out x
    | Subst x -> K.Subst.pp out x
    | Theory x -> K.Theory.pp out x
    | Chunk c ->
      if short then Fmt.string out "<chunk>" else pp_chunk out c
    | Prim p -> pp_prim out p

  and pp_chunk ?ip out (self:chunk) : unit =
    let ppi ppx out (i,x) =
      let ptr = match ip with Some i' when i=i' -> ">" | _ -> " " in
      Fmt.fprintf out "%s%-8d %a" ptr i ppx x in
    Fmt.fprintf out "@[<v2>chunk[%d] {@ %a@ :locals@ %a@;<1 -2>}@]"
      self.c_n_regs
      (pp_arri ~sep:"" @@ ppi VM_instr.pp) self.c_instrs
      (pp_arri ~sep:"" @@ ppi @@ pp_value ~short:true) self.c_locals

  and pp_prim out (p:primitive) : unit =
    Fmt.fprintf out "<prim %s>" p.pr_name
end

type vm = Types_.vm

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
  let prim p : t = Prim p

  let pp = pp_value ~short:false
  let pp_short = pp_value ~short:true
  let show = Fmt.to_string pp

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

  let[@inline] mem k self = Str_map.mem k self.env
  let[@inline] add s v self : t = {env=Str_map.add s v self.env}
  let[@inline] find s self = Str_map.find_opt s self.env
  let[@inline] iter self = Str_map.to_iter self.env
end

module Chunk = struct
  open Types_
  type t = chunk
  let pp out c = pp_chunk out c
  let pp_at ~ip out c = pp_chunk ~ip out c

  (* empty chunk, does nothing *)
  let dummy : t = {
    c_n_regs=0;
    c_locals=[||];
    c_instrs=[||];
  }
end

module Primitive = struct
  open Types_
  type t = primitive

  let[@inline] name p = p.pr_name
  let pp = pp_prim
  let make ~name ~eval () : t =
    { pr_name=name; pr_eval=eval; }
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
  let[@inline] pop_val_exn (self:t) : Value.t =
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

  let[@inline] extract_ (self:t) i =
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

  let dump out (self:t) : unit =
    let {
      stack; call_stack; ip; call_restore_ip;
      call_reg_start; call_prim;
      regs; env=_ } = self in
    Fmt.fprintf out "@[<v2>VM {@ ";
    Fmt.fprintf out "@[call stack: %d frames@]@," (Vec.size call_stack);
    if not (Vec.is_empty call_stack) then (
      Fmt.fprintf out "@[<v>top chunk:@ ";
      Chunk.pp_at ~ip out (Vec.last_exn call_stack);
      Fmt.fprintf out "@]@,";
    );

    Fmt.fprintf out "@[<v2>operand stack:@ ";
    Vec.iteri (fun i v ->
        if i>0 then Fmt.fprintf out "@,";
        Fmt.fprintf out "[%d]: %a" i Value.pp_short v)
      stack;
    Fmt.fprintf out "@]@,";

    ignore regs;
    ignore call_reg_start;
    ignore regs; (* TODO: display them for current frame *)

    Fmt.fprintf out "@;<1 -2>}@]"

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

          | Dup ->
            if Vec.is_empty self.stack then (
              Error.fail "vm.dup: stack underflow"
            );
            let v = Vec.last_exn self.stack in
            push_val self v

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
              | _ -> Error.fail "vm.not: type error"
            end

          | Add ->
            let b = pop_val_exn self in
            let a = pop_val_exn self in
            begin match a, b with
              | Int a, Int b ->
                push_val self (Value.int (a+b))
              | _ -> Error.fail "vm.add: type error"
            end

          | Add1 ->
            let a = pop_val_exn self in
            begin match a with
              | Int a -> push_val self (Value.int (a+1))
              | _ -> Error.fail "vm.add1: type error"
            end

          | Sub ->
            let b = pop_val_exn self in
            let a = pop_val_exn self in
            begin match a, b with
              | Int a, Int b ->
                push_val self (Value.int (a-b))
              | _ -> Error.fail "vm.sub: type error"
            end
          | Sub1 ->
            let a = pop_val_exn self in
            begin match a with
              | Int a -> push_val self (Value.int (a-1))
              | _ -> Error.fail "vm.sub1: type error"
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
              | _ -> Error.fail "vm.jlt: type error"
            end

          | Jleq ip ->

            let b = pop_val_exn self in
            let a = pop_val_exn self in
            begin match a, b with
              | Int a, Int b -> if a <= b then self.ip <- ip;
              | _ -> Error.fail "vm.jleq: type error"
            end

          | Jmp ip ->
            self.ip <- ip

          | Memenv ->
            let key = pop_val_exn self in
            begin match key with
              | String v ->
                let b = Value.bool (Env.mem v self.env) in
                push_val self b
              | _ -> Error.fail "vm.memenv: required a string"
            end

          | Getenv ->
            let key = pop_val_exn self in
            begin match key with
              | String v ->
                begin match Env.find v self.env with
                  | Some x -> push_val self x
                  | None -> Error.fail "vm.getenv: key not present"
                end
              | _ -> Error.fail "vm.getenv: required a string"
            end

          | Qenv ->
            let key = pop_val_exn self in
            begin match key with
              | String v ->
                begin match Env.find v self.env with
                  | Some x ->
                    push_val self x;
                    push_val self (Value.bool true);
                  | None ->
                    push_val self Value.nil;
                    push_val self (Value.bool false);
                end
              | _ -> Error.fail "vm.qenv: required a string"
            end
        )
      done
    with Stop_exec ->
      ()
end

(* chunk builder. temporary structure to construct chunks. *)
module Chunk_builder_ = struct
  open Types_
  type t = {
    cb_instrs: instr Vec.t; (** Instructions *)
    mutable cb_n_regs: int; (** Number of regs to allocate for this chunk *)
    cb_locals: value Vec.t; (** Local values, used by some instructions *)
  }

  let create() : t =
    { cb_instrs=Vec.create(); cb_n_regs=0; cb_locals=Vec.create(); }

  let reset (self:t) : unit =
    let {cb_instrs; cb_locals; cb_n_regs=_} = self in
    self.cb_n_regs <- 0;
    Vec.clear cb_instrs;
    Vec.clear cb_locals;
    ()

  let to_chunk (self:t) : chunk =
    { c_instrs=Vec.to_array self.cb_instrs;
      c_n_regs=self.cb_n_regs;
      c_locals=Vec.to_array self.cb_locals; }

  let[@inline] add_local (self:t) (v:value) : int =
    let i = Vec.size self.cb_locals in
    Vec.push self.cb_locals v;
    i

  let add_instr self (i:instr) : unit =
    Vec.push self.cb_instrs i;
    begin match i with
      | Rstore i | Rload i -> self.cb_n_regs <- max (i+1) self.cb_n_regs
      | Nop | Call | Ret | Dup | Drop | Exch | Extract _
      | Lload _ | Int _ | Memenv | Getenv | Qenv
      | Bool _ | Nil | Not | Add | Add1 | Sub | Sub1 | Jeq _ | Jlt _
      | Jleq _ | Jmp _ -> ()
    end

  (* current position in the list of instructions *)
  let cur_pos (self:t) : int =
    Vec.size self.cb_instrs

  (* set an instruction after the fact *)
  let set_instr (self:t) i (instr:instr) : unit =
    assert (i < Vec.size self.cb_instrs);
    Vec.set self.cb_instrs i instr
end

module Parser = struct
  open Types_
  module CB = Chunk_builder_

  type t = {
    str: string;
    prims: Primitive.t Str_map.t;
  }

  let create ?(prims=Str_map.empty) (str:string) : t =
    {str; prims}

  type st = {
    buf: Lexing.lexbuf;
    prims: Primitive.t Str_map.t;
    cb: CB.t;
    delayed: (unit -> unit) Vec.t; (* set instructions based on labels *)
    mutable labels: int Str_map.t; (* offset of labels *)
  }

  let create_st prims buf : st =
    { buf;
      prims;
      cb = CB.create();
      delayed=Vec.create();
      labels=Str_map.empty;
    }

  let exact self what tok =
    let tok' = VM_lex.token self.buf in
    if tok <> tok' then Error.failf (fun k->k"expected %s" what)

  let int self = match VM_lex.token self.buf with
    | VM_lex.INT i -> int_of_string i
    | _ -> Error.fail "expected integer"
  let label self = match VM_lex.token self.buf with
    | VM_lex.COLON_STR s -> s
    | _ -> Error.fail "expected label (e.g. `:foo`)"

  let between_angle self p =
    exact self "'<'" VM_lex.LANGLE;
    let x=p self in
    exact self "'>'" VM_lex.RANGLE;
    x

  let rec parse_into (self:st) : [`Eoi | `Rbrace] =
    let[@inline] recurse() = parse_into self in

    let finalize() =
      Vec.iter (fun d -> d()) self.delayed;
      Vec.clear self.delayed
    in

    (* call [f] with the address of [lbl] *)
    let with_label lbl f =
      Vec.push self.delayed
        (fun () ->
           match Str_map.find_opt lbl self.labels with
           | None -> Error.failf (fun k->k"cannot find label %S" lbl)
           | Some i -> f i)
    in

    match VM_lex.token self.buf with
    | VM_lex.QUOTED_STR s ->
      let n = CB.add_local self.cb (Value.string s) in
      CB.add_instr self.cb (Instr.Lload n);
      recurse()

    | VM_lex.COLON_STR lbl ->
      (* remember position of label *)
      self.labels <- Str_map.add lbl (CB.cur_pos self.cb) self.labels;
      recurse();

    | VM_lex.LPAREN -> Error.fail "syntax error"
    | VM_lex.RPAREN -> Error.fail "syntax error"
    | VM_lex.LBRACKET -> Error.fail "syntax error"
    | VM_lex.RBRACKET -> Error.fail "syntax error"
    | VM_lex.LANGLE -> Error.fail "syntax error"
    | VM_lex.RANGLE -> Error.fail "syntax error"

    | VM_lex.INT i ->
      let i = int_of_string i in
      CB.add_instr self.cb (Instr.Int i);
      recurse()

    | VM_lex.ATOM str ->
      begin match str with
        | "nop" -> CB.add_instr self.cb Instr.Nop
        | "call" -> CB.add_instr self.cb Instr.Call
        | "ret" -> CB.add_instr self.cb Instr.Ret
        | "dup" -> CB.add_instr self.cb Instr.Dup
        | "drop" -> CB.add_instr self.cb Instr.Drop
        | "exch" -> CB.add_instr self.cb Instr.Exch
        | "extract" ->
          let i = between_angle self int in
          CB.add_instr self.cb (Instr.Extract i)
        | "rstore" ->
          let i = between_angle self int in
          CB.add_instr self.cb (Instr.Rstore i)
        | "rload" ->
          let i = between_angle self int in
          CB.add_instr self.cb (Instr.Rload i)
        | "lload" ->
          let i = between_angle self int in
          CB.add_instr self.cb (Instr.Lload i)
        | "true" -> CB.add_instr self.cb (Instr.Bool true)
        | "false" -> CB.add_instr self.cb (Instr.Bool false)
        | "nil" -> CB.add_instr self.cb Instr.Nil
        | "not" ->  CB.add_instr self.cb Instr.Not
        | "add" -> CB.add_instr self.cb Instr.Add
        | "add1" -> CB.add_instr self.cb Instr.Add1
        | "sub" -> CB.add_instr self.cb Instr.Sub
        | "sub1" -> CB.add_instr self.cb Instr.Sub1
        | "jeq" ->
          let lbl = between_angle self label in
          let cur_pos = CB.cur_pos self.cb in
          CB.add_instr self.cb Instr.Nop;
          with_label lbl (fun lbl_pos ->
              CB.set_instr self.cb cur_pos (Instr.Jeq lbl_pos))

        | "jlt" ->
          let lbl = between_angle self label in
          let cur_pos = CB.cur_pos self.cb in
          CB.add_instr self.cb Instr.Nop;
          with_label lbl (fun lbl_pos ->
              CB.set_instr self.cb cur_pos (Instr.Jlt lbl_pos))

        | "jleq" ->
          let lbl = between_angle self label in
          let cur_pos = CB.cur_pos self.cb in
          CB.add_instr self.cb Instr.Nop;
          with_label lbl (fun lbl_pos ->
              CB.set_instr self.cb cur_pos (Instr.Jleq lbl_pos))

        | "jmp" ->
          let lbl = between_angle self label in
          let cur_pos = CB.cur_pos self.cb in
          CB.add_instr self.cb Instr.Nop;
          with_label lbl (fun lbl_pos ->
              CB.set_instr self.cb cur_pos (Instr.Jmp lbl_pos))

        | "memenv" -> CB.add_instr self.cb Instr.Memenv
        | "getenv" -> CB.add_instr self.cb Instr.Getenv
        | "qenv" -> CB.add_instr self.cb Instr.Qenv
        | _ ->
          begin match Str_map.find_opt str self.prims with
            | Some p ->
              (* load primitive *)
              let n = CB.add_local self.cb (Value.prim p) in
              CB.add_instr self.cb (Instr.Lload n);
              CB.add_instr self.cb Instr.Call;
            | None ->
              Error.failf (fun k->k"unknown instruction/prim %S" str)
          end
      end;
      recurse()

    | VM_lex.LBRACE ->
      (* parse sub-chunk *)
      let st' = create_st self.prims self.buf in
      begin match parse_into st' with
        | `Eoi -> Error.fail "expected '}'"
        | `Rbrace ->
          (* finish sub-chunk, put it into locals *)
          let c = CB.to_chunk st'.cb in
          let n = CB.add_local self.cb (Value.chunk c) in
          CB.add_instr self.cb (Instr.Lload n);
          recurse()
      end
    | VM_lex.RBRACE -> finalize(); `Rbrace
    | VM_lex.EOI -> finalize(); `Eoi

  let parse (self:t) : _ result =
    let buf = Lexing.from_string ~with_positions:false self.str in
    let st = create_st self.prims buf in

    begin match parse_into st with
      | `Eoi ->
        let c = CB.to_chunk st.cb in
        Ok c
      | `Rbrace -> Error.fail "unterminated input"
      | exception Error.E err -> Error err
      | exception Failure msg -> Error (Error.make msg)
      | exception e ->
        Error (Error.of_exn e)
    end
end

(* TODO: expose instructions so that ITP can use its own syntax for VM? *)

type t = Types_.vm

let create ?(env=Env.empty) () : t =
  let vm = VM_.create env in
  vm

let[@inline] get_env (self:t) = self.env
let[@inline] set_env (self:t) e = self.env <- e

let reset = VM_.reset
let push = VM_.push_val
let pop = VM_.pop_val
let pop_exn = VM_.pop_val_exn
let run self c =
  VM_.enter_chunk self c;
  VM_.run self

let dump = VM_.dump

let parse_string ?prims s : _ result =
  let p = Parser.create ?prims s in
  Parser.parse p

let parse_string_exn ?prims s : Chunk.t =
  match parse_string ?prims s with
  | Ok c -> c
  | Error e -> Error.raise e

(*$R
  let c = parse_string_exn "42 2 add" in
  let vm = create () in
  run vm c;
  let v = pop_exn vm in
  assert_equal ~cmp:Value.equal ~printer:Value.show (Value.int 44) v
    *)
