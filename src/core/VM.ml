open Sigs
module K = Kernel

type 'a vec = 'a Vec.t

(* all types *)
module Types_ = struct
  type vm = {
    stack: value Vec.t;  (** Operand stack. *)
    stack_offsets: int Vec.t;  (** End offset for each frame in `stack` *)
    call_stack: chunk Vec.t;
        (** Chunks currently being evaluated. The active chunk is the one
        on top. *)
    mutable ip: int;
        (** Instruction pointer for topmost chunk in {!call_stack} *)
    call_restore_ip: int Vec.t;
        (** IP for all items in [call_stack] except the last. *)
    call_prim: primitive Vec.t;  (** Primitives currently being evaluated *)
    regs: value Vec.t;
        (** Stack of register value. Each call frame has its own
        local register. *)
    ctx: K.Ctx.t;  (** Logical context *)
    mutable debug_hook: (vm -> instr -> unit) option;
  }

  and thunk = { mutable th_st: thunk_state }

  and thunk_state =
    | Th_ok of value list
    | Th_err of Error.t
    | Th_lazy of chunk
    | Th_suspended of {
        c: chunk;
        vm: vm;
      }

  and call_item =
    | C_chunk of {
        c: chunk;
        mutable ip: int;  (** Value of [ip] in that chunk *)
      }
    | C_prim of primitive

  and value =
    | Nil
    | Bool of bool
    | Int of int
    | String of string
    | Array of value vec
    | Expr of K.Expr.t
    | Seq of K.Sequent.t
    | Thm of K.Thm.t
    | Var of K.Var.t
    | Const of K.Const.t
    | Subst of K.Subst.t
    | Theory of K.Theory.t
    | Chunk of chunk
    | Thunk of thunk
    | Prim of primitive

  and primitive = {
    pr_name: string;
    pr_eval: vm -> unit;
  }
  (** Primitive implemented in OCaml *)

  (* list of instructions; the atomic block of code *)
  and chunk = {
    c_instrs: instr array;  (** Instructions *)
    c_n_args: int;  (** Number of parameters *)
    c_n_ret: int;  (** Number of values returned *)
    c_n_regs: int;  (** Number of regs to allocate for this chunk *)
    c_locals: value array;  (** Local values, used by some instructions *)
    mutable c_comments: (int * string) array;  (** comments *)
  }

  and instr = VM_instr_.t

  let pp_vec ?(sep = ", ") ppx out v =
    Fmt.fprintf out "%a" (pp_iter ~sep ppx) (Vec.to_iter v)

  let pp_arri ?(sep = ", ") ppx out a =
    Fmt.fprintf out "%a" (pp_iter ~sep ppx) (Iter.of_array_i a)

  let rec pp_value ~short out = function
    | Nil -> Fmt.string out "nil"
    | Bool x -> Fmt.bool out x
    | Int x -> Fmt.int out x
    | String x -> Fmt.fprintf out "%S" x
    | Array x ->
      Fmt.fprintf out "[@[%a@]]" (pp_vec ~sep:", " @@ pp_value ~short) x
    | Expr x -> K.Expr.pp out x
    | Thm x -> K.Thm.pp out x
    | Seq x -> K.Sequent.pp out x
    | Var x -> K.Var.pp out x
    | Const x -> K.Const.pp out x
    | Subst x -> K.Subst.pp out x
    | Theory x -> K.Theory.pp out x
    | Chunk c ->
      if short then
        Fmt.string out "<chunk>"
      else
        pp_chunk out c
    | Thunk th -> pp_thunk out th
    | Prim p -> pp_prim out p

  and pp_thunk_state ~short out = function
    | Th_ok v -> Fmt.fprintf out "(@[ok %a@])" (pp_list @@ pp_value ~short) v
    | Th_err e -> Fmt.fprintf out "(@[err %a@])" Error.pp e
    | Th_lazy _ when short -> Fmt.string out "(lazy)"
    | Th_lazy c ->
      (* print chunk, but do not print thunks inside recursively *)
      Fmt.fprintf out "(@[lazy@ %a@])" (pp_chunk ?ip:None) c
    | Th_suspended _c when short -> Fmt.string out "(suspended)"
    | Th_suspended { c; vm } ->
      Fmt.fprintf out "(@[suspended %a@])" (pp_chunk ~ip:vm.ip) c

  and pp_thunk out (self : thunk) =
    Fmt.fprintf out "(@[thunk@ :st %a@])"
      (pp_thunk_state ~short:true)
      self.th_st

  and debug_thunk out (self : thunk) =
    Fmt.fprintf out "(@[thunk@ :st %a@])"
      (pp_thunk_state ~short:false)
      self.th_st

  and pp_chunk ?ip out (self : chunk) : unit =
    let pp_instr i out instr =
      VM_instr_.pp out instr;
      match instr with
      | Lload n ->
        let local = self.c_locals.(n) in
        Fmt.fprintf out " ; %a" (pp_value ~short:true) local
      | _ ->
        (match
           CCArray.bsearch (i, "")
             ~cmp:(fun (i, _) (j, _) -> compare i j)
             self.c_comments
         with
        | `At j ->
          let _, comment = self.c_comments.(j) in
          Fmt.fprintf out " ; %s" comment
        | _ -> ())
    in
    let ppi pre ppx out (i, x) = Fmt.fprintf out "%s%-8d %a" pre i ppx x in
    let ppi_ip ppx out (i, x) =
      let ptr =
        match ip with
        | Some i' when i = i' -> ">"
        | _ -> " "
      in
      ppi ptr (ppx i) out (i, x)
    in
    let pp_locals out () =
      if Array.length self.c_locals = 0 then
        ()
      else
        Fmt.fprintf out "@ :locals@ %a"
          (pp_arri ~sep:"" @@ ppi " " @@ pp_value ~short:false)
          self.c_locals
    in
    Fmt.fprintf out "@[<v2>chunk[%d->%d|%d local] {@ :instrs@ %a%a@;<1 -2>}@]"
      self.c_n_args self.c_n_ret self.c_n_regs
      (pp_arri ~sep:"" @@ ppi_ip pp_instr)
      self.c_instrs pp_locals ()

  and debug_chunk ?ip out c = pp_chunk ?ip out c

  and pp_prim out (p : primitive) : unit = Fmt.fprintf out "<prim %s>" p.pr_name
end

type vm = Types_.vm

type thunk = Types_.thunk

type chunk = Types_.chunk

type primitive = Types_.primitive

(* auto generated instructions *)
module Instr = struct
  open Types_

  type t = instr

  (* builder *)
  include VM_instr_.Build

  let pp = VM_instr_.pp

  let to_string = Fmt.to_string pp
end

module Value = struct
  open Types_

  type t = value

  let nil : t = Nil

  let bool b : t = Bool b

  let true_ = bool true

  let false_ = bool false

  let int (x : int) : t = Int x

  let string (x : string) : t = String x

  let array (x : t vec) : t = Array x

  let expr (x : K.Expr.t) : t = Expr x

  let thm (x : K.Thm.t) : t = Thm x

  let seq seq : t = Seq seq

  let var (x : K.Var.t) : t = Var x

  let const (x : K.Const.t) : t = Const x

  let subst (x : K.Subst.t) : t = Subst x

  let theory (x : K.Theory.t) : t = Theory x

  let chunk c : t = Chunk c

  let thunk th : t = Thunk th

  let prim p : t = Prim p

  let pp = pp_value ~short:false

  let pp_short = pp_value ~short:true

  let show = Fmt.to_string pp

  let rec equal a b =
    match a, b with
    | Nil, Nil -> true
    | Bool b1, Bool b2 -> b1 = b2
    | Int i, Int j -> i = j
    | String s1, String s2 -> s1 = s2
    | Array v1, Array v2 -> Vec.equal equal v1 v2
    | Expr e1, Expr e2 -> K.Expr.equal e1 e2
    | Thm th1, Thm th2 -> K.Thm.equal th1 th2
    | Var v1, Var v2 -> K.Var.equal v1 v2
    | Const c1, Const c2 -> K.Const.equal c1 c2
    | Subst s1, Subst s2 -> K.Subst.equal s1 s2
    | Theory th1, Theory th2 -> th1 == th2
    | Chunk c1, Chunk c2 -> c1 == c2
    | Thunk th1, Thunk th2 -> th1 == th2
    | Seq s1, Seq s2 -> K.Sequent.equal s1 s2
    | Prim p1, Prim p2 -> p1.pr_name = p2.pr_name
    | ( ( Bool _ | Int _ | String _ | Array _ | Const _ | Expr _ | Thm _ | Var _
        | Subst _ | Thunk _ | Seq _ | Theory _ | Nil | Chunk _ | Prim _ ),
        _ ) ->
      false

  type 'a conv_to = t -> 'a option

  type 'a conv_to_exn = t -> 'a

  let[@inline] to_str = function
    | String x -> Some x
    | _ -> None

  let[@inline] to_bool = function
    | Bool x -> Some x
    | _ -> None

  let[@inline] to_int = function
    | Int x -> Some x
    | _ -> None

  let[@inline] to_expr = function
    | Expr x -> Some x
    | _ -> None

  let[@inline] to_thm = function
    | Thm x -> Some x
    | _ -> None

  let[@inline] to_seq = function
    | Seq x -> Some x
    | _ -> None

  let[@inline] to_var = function
    | Var x -> Some x
    | _ -> None

  let[@inline] to_const = function
    | Const x -> Some x
    | _ -> None

  let[@inline] to_array = function
    | Array x -> Some x
    | _ -> None

  let[@inline] to_subst = function
    | Subst x -> Some x
    | _ -> None

  let[@inline] to_thunk = function
    | Thunk x -> Some x
    | _ -> None

  let[@inline] to_str_exn = function
    | String x -> x
    | _ -> Error.fail "expected string"

  let[@inline] to_bool_exn = function
    | Bool x -> x
    | _ -> Error.fail "expected bool"

  let[@inline] to_int_exn = function
    | Int x -> x
    | _ -> Error.fail "expected int"

  let[@inline] to_expr_exn = function
    | Expr x -> x
    | _ -> Error.fail "expected expr"

  let[@inline] to_thm_exn = function
    | Thm x -> x
    | _ -> Error.fail "expected thm"

  let[@inline] to_seq_exn = function
    | Seq x -> x
    | _ -> Error.fail "expected sequent"

  let[@inline] to_var_exn = function
    | Var x -> x
    | _ -> Error.fail "expected var"

  let[@inline] to_const_exn = function
    | Const x -> x
    | _ -> Error.fail "expected const"

  let[@inline] to_array_exn = function
    | Array x -> x
    | _ -> Error.fail "expected array"

  let[@inline] to_subst_exn = function
    | Subst x -> x
    | _ -> Error.fail "expected subst"

  let[@inline] to_thunk_exn = function
    | Thunk x -> x
    | _ -> Error.fail "expected thunk"
end

module Chunk = struct
  open Types_

  type t = chunk

  let pp out c = pp_chunk out c

  let to_string = Fmt.to_string pp

  let pp_at ~ip out c = pp_chunk ~ip out c

  let debug = debug_chunk ?ip:None

  let strip_comments self = self.c_comments <- [||]

  (* empty chunk, does nothing *)
  let dummy : t =
    {
      c_n_regs = 0;
      c_locals = [||];
      c_n_args = 0;
      c_n_ret = 0;
      c_instrs = [||];
      c_comments = [||];
    }
end

module Primitive = struct
  open Types_

  type t = primitive

  let[@inline] name p = p.pr_name

  let pp = pp_prim

  let to_string = Fmt.to_string pp

  let make ~name ~eval () : t = { pr_name = name; pr_eval = eval }
end

module Thunk = struct
  open Types_

  type t = thunk

  let[@inline] state self = self.th_st

  let resolved self =
    match state self with
    | Th_ok _ | Th_err _ -> true
    | Th_lazy _ | Th_suspended _ -> false

  let get_result_exn self =
    match state self with
    | Th_ok v -> Stdlib.Ok v
    | Th_err e -> Stdlib.Error e
    | Th_suspended _ | Th_lazy _ -> assert false

  let pp_state = pp_thunk_state

  let pp = pp_thunk

  let debug = debug_thunk

  let to_string = Fmt.to_string pp

  let make c : t = { th_st = Th_lazy c }
end

module Stanza = struct
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
    | Define_thunk of {
        name: string;
        value: Thunk.t;
      }  (** Define a meta-level chunk *)
    | Define_chunk of {
        name: string;
        value: Chunk.t;
      }  (** Define a meta-level chunk *)
    | Eval of { value: Thunk.t }

  type t = {
    id: Sym_ptr.t;
    view: view;
  }

  let[@inline] view self = self.view

  let[@inline] make ~id view : t = { view; id }

  let[@inline] id self = self.id

  let pp_with ~pp_thunk out (self : t) : unit =
    match view self with
    | Declare { name; ty } ->
      Fmt.fprintf out "(@[declare %s@ :ty %a@])" name pp_thunk ty
    | Define { name; body } ->
      Fmt.fprintf out "(@[define %s@ :body %a@])" name pp_thunk body
    | Define_thunk { name; value } ->
      Fmt.fprintf out "(@[def `%s`@ %a@])" name pp_thunk value
    | Define_chunk { name; value } ->
      Fmt.fprintf out "(@[def `%s`@ %a@])" name Chunk.pp value
    | Prove { name; deps; goal; proof } ->
      let pp_dep out (s, kind, ref) =
        let skind =
          match kind with
          | `Eager -> ":eager"
          | `Lazy -> ":lazy"
        in
        Fmt.fprintf out "(@[%s %s %s@ :goal %a@ :proof %a@])" s skind ref
          pp_thunk goal pp_thunk proof
      in
      Fmt.fprintf out "(@[prove %s@ :deps (@[%a@])@])" name (pp_list pp_dep)
        deps
    | Eval { value } -> Fmt.fprintf out "(@[eval@ %a@])" pp_thunk value

  let pp = pp_with ~pp_thunk:Thunk.pp

  let debug = pp_with ~pp_thunk:Thunk.debug
end

(** Exceptions raised to suspend a computation so as to compute
    a required thunk *)

exception Suspend_and_eval_chunk of Thunk.t * Chunk.t

exception Suspend_and_resume of Thunk.t * Chunk.t * vm

(* internal handling of the VM *)
module VM_ = struct
  open Types_

  type t = vm

  (* exception used in instructions to stop execution right now.
     This doesn't unwind the stack.

     Caution: this must only be raised from within the VM, i.e. within
     an instruction. *)
  exception Stop_exec

  let create ~ctx : t =
    {
      stack = Vec.make 128 Value.nil;
      stack_offsets = Vec.make 128 0;
      call_stack = Vec.make 12 Chunk.dummy;
      call_restore_ip = Vec.make 12 0;
      call_prim = Vec.create ();
      ip = 0;
      regs = Vec.make 32 Value.nil;
      ctx;
      debug_hook = None;
    }

  let[@inline] push_val (self : t) v = Vec.push self.stack v

  let push_vals (self : t) l = List.iter (Vec.push self.stack) l

  let[@inline] pop_val (self : t) = Vec.pop self.stack

  let[@inline] pop_val_exn (self : t) : Value.t =
    if Vec.is_empty self.stack then Error.fail "vm.pop: operand stack is empty";
    Vec.pop_exn self.stack

  let pop_vals (self : t) : Value.t list =
    let l = Vec.to_list self.stack in
    Vec.clear self.stack;
    l

  let swap_val (self : t) =
    if Vec.size self.stack < 2 then
      Error.fail "vm.swap: operand stack too small";
    let v1 = Vec.pop_exn self.stack in
    let v2 = Vec.pop_exn self.stack in
    Vec.push self.stack v1;
    Vec.push self.stack v2

  let[@inline] extract_ (self : t) i =
    if i >= Vec.size self.stack then
      Error.fail "vm.extract: operand stack too small";
    let v = Vec.get self.stack (Vec.size self.stack - i - 1) in
    Vec.push self.stack v

  (* reset state entirely *)
  let reset (self : t) : unit =
    let {
      stack;
      call_stack;
      ip = _;
      call_prim;
      stack_offsets;
      call_restore_ip;
      regs;
      ctx = _;
      debug_hook = _;
    } =
      self
    in
    self.ip <- 0;
    Vec.clear call_stack;
    Vec.clear call_restore_ip;
    Vec.clear stack;
    Vec.clear call_prim;
    Vec.clear regs;
    Vec.clear stack_offsets;
    self.debug_hook <- None;
    ()

  (* enter chunk, passing it [n] arguments off the stack *)
  let enter_chunk (self : t) (c : chunk) ~n : unit =
    if n <> c.c_n_args then
      Error.failf (fun k ->
          k "vm.enter_chunk: expected %d arguments, got %d" c.c_n_args n);
    if n > c.c_n_regs then
      Error.failf (fun k -> k "vm.enter_chunk: too many arguments");
    if not (Vec.is_empty self.call_stack) then
      Vec.push self.call_restore_ip self.ip;
    self.ip <- 0;
    Vec.push self.call_stack c;
    (* allocate registers *)
    let start_regs = Vec.size self.regs in
    Vec.ensure_size self.regs Value.nil (start_regs + c.c_n_regs);
    (* move [n] values from stack to regs for [c], before allocating
       a new operand stack frame *)
    for j = n downto 1 do
      let v = pop_val_exn self in
      Vec.set self.regs (start_regs + j - 1) v
    done;
    (* alloc operand stack frame *)
    Vec.push self.stack_offsets (Vec.size self.stack)

  (* return [n] values from chunk *)
  let exit_chunk (self : t) : unit =
    let c = Vec.pop_exn self.call_stack in
    if c.c_n_regs > 0 then Vec.shrink self.regs (Vec.size self.regs - c.c_n_regs);
    assert (not (Vec.is_empty self.stack_offsets));

    let n_ret = c.c_n_ret in

    (* return [n] values to caller *)
    let last_stack_off = Vec.pop_exn self.stack_offsets in
    let frame_size = Vec.size self.stack - last_stack_off in
    if frame_size < n_ret then
      Error.failf (fun k ->
          k "vm.exit_chunk: must return %d values,@ frame only contains %d"
            frame_size n_ret);
    if frame_size <> n_ret then (
      (* shift items on the stack, the [frame_size-n] bottom ones in the top
         frame must be discarded *)
      let arr = Vec.unsafe_array_ self.stack in
      if n_ret > 0 then
        Array.blit arr
          (last_stack_off + frame_size - n_ret)
          arr last_stack_off n_ret;
      Vec.shrink self.stack (last_stack_off + n_ret)
    );

    (* restore instruction pointer *)
    if not (Vec.is_empty self.call_restore_ip) then (
      assert (not (Vec.is_empty self.call_stack));
      self.ip <- Vec.pop_exn self.call_restore_ip
    )

  let eval_prim (self : t) (p : primitive) : unit =
    let len = Vec.size self.call_stack in
    Vec.push self.call_prim p;
    p.pr_eval self;
    let len' = Vec.size self.call_stack in
    if len' <> len then
      Error.failf (fun k ->
          k "vm.eval-prim: call stack changed (size %d->%d)" len len');
    match Vec.pop self.call_prim with
    | Some p' -> assert (p == p')
    | _ -> Error.fail "vm.eval-prim: mismatched current primitive"

  let rload (self : t) (i : int) : Value.t =
    let c = Vec.last_exn self.call_stack in
    let n = c.c_n_regs in
    if i >= n then Error.fail "vm.rload: invalid register";
    Vec.get self.regs (Vec.size self.regs - n + i)

  let rstore (self : t) (i : int) v : unit =
    let c = Vec.last_exn self.call_stack in
    let n = c.c_n_regs in
    if i >= n then Error.fail "vm.rstore: not enough registers";
    Vec.set self.regs (Vec.size self.regs - n + i) v

  let dump out (self : t) : unit =
    let {
      stack;
      call_stack;
      ip;
      call_restore_ip = _;
      call_prim = _;
      stack_offsets = _;
      ctx = _;
      debug_hook = _;
      regs;
    } =
      self
    in
    Fmt.fprintf out "@[<v2>VM {@ ";
    Fmt.fprintf out "@[call stack: %d frames@]" (Vec.size call_stack);

    if not (Vec.is_empty call_stack) then (
      let c = Vec.last_exn call_stack in
      Fmt.fprintf out "@,@[<v2>top chunk: {@ ";
      Chunk.pp_at ~ip out c;

      (* print registers *)
      assert (Vec.size self.regs >= c.c_n_regs);
      if c.c_n_regs > 0 then
        for i = 0 to c.c_n_regs - 1 do
          let v = Vec.get regs (Vec.size regs - c.c_n_regs + i) in
          Fmt.fprintf out "@,reg[%d]: %a" i Value.pp_short v
        done;

      Fmt.fprintf out "@;<1 -2>}@]"
    );

    if Vec.is_empty stack then
      Fmt.fprintf out "@,operand stack: []"
    else (
      Fmt.fprintf out "@,@[<v2>operand stack: [@ ";
      Vec.iteri
        (fun i v ->
          if i > 0 then Fmt.fprintf out "@,";
          Fmt.fprintf out "[%d]: %a" i Value.pp_short v)
        stack;
      Fmt.fprintf out "@;<1 -2>]@]"
    );

    Fmt.fprintf out "@;<1 -2>}@]"

  let run (self : t) : unit =
    let continue = ref true in
    try
      while !continue do
        let ip = self.ip in
        assert (ip >= 0);
        let c = Vec.last_exn self.call_stack in

        if ip >= Array.length c.c_instrs then (
          (* done with chunk *)
          exit_chunk self;
          if Vec.is_empty self.call_stack then continue := false (* all done *)
        ) else (
          (* execute current instruction in [c] *)
          let instr = Array.unsafe_get c.c_instrs ip in

          (match self.debug_hook with
          | None -> ()
          | Some h -> h self instr);

          self.ip <- self.ip + 1;

          (* preemptively advance by 1 *)
          match instr with
          | Nop -> ()
          | Ret ->
            exit_chunk self;
            if Vec.is_empty self.call_stack then continue := false
          | Drop -> ignore (pop_val_exn self : Value.t)
          | Exch -> swap_val self
          | Extract i -> extract_ self i
          | Dup ->
            if Vec.is_empty self.stack then Error.fail "vm.dup: stack underflow";
            let v = Vec.last_exn self.stack in
            push_val self v
          | Int i -> push_val self (Value.int i)
          | Bool b -> push_val self (Value.bool b)
          | Nil -> push_val self Value.nil
          | Call n ->
            let c = pop_val_exn self in
            (match c with
            | Chunk c -> enter_chunk self c ~n
            | Prim p ->
              (* FIXME: pass arguments to prim via a list of [n] values *)
              eval_prim self p
            | _ ->
              Error.failf (fun k ->
                  k "call: expected a chunk,@ got %a" Value.pp c))
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
            ) else
              Error.fail "vm.lload: invalid index"
          | Not ->
            let a = pop_val_exn self in
            (match a with
            | Bool b -> push_val self (Value.bool (not b))
            | _ -> Error.fail "vm.not: type error")
          | Add ->
            let b = pop_val_exn self |> Value.to_int_exn in
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a + b))
          | Add1 ->
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a + 1))
          | Sub ->
            let b = pop_val_exn self |> Value.to_int_exn in
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a - b))
          | Sub1 ->
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a - 1))
          | Mult ->
            let b = pop_val_exn self |> Value.to_int_exn in
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a * b))
          | Eq ->
            let b = pop_val_exn self in
            let a = pop_val_exn self in
            push_val self (Value.bool (Value.equal a b))
          | Leq ->
            let b = pop_val_exn self |> Value.to_int_exn in
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.bool (a <= b))
          | Lt ->
            let b = pop_val_exn self |> Value.to_int_exn in
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.bool (a < b))
          | Jif ip ->
            let x = pop_val_exn self |> Value.to_bool_exn in
            if x then self.ip <- ip
          | Jifn ip ->
            let x = pop_val_exn self |> Value.to_bool_exn in
            if not x then self.ip <- ip
          | Jmp ip -> self.ip <- ip
          | Acreate -> push_val self @@ Value.array (Vec.create ())
          | Apush ->
            let x = pop_val_exn self in
            let arr = pop_val_exn self |> Value.to_array_exn in
            Vec.push arr x
          | Aget ->
            let i = pop_val_exn self |> Value.to_int_exn in
            let arr = pop_val_exn self |> Value.to_array_exn in
            push_val self @@ Vec.get arr i
          | Aset ->
            let x = pop_val_exn self in
            let i = pop_val_exn self |> Value.to_int_exn in
            let arr = pop_val_exn self |> Value.to_array_exn in
            Vec.set arr i x
          | Alen ->
            let arr = pop_val_exn self |> Value.to_array_exn in
            push_val self (Value.int @@ Vec.size arr)
          | Aclear ->
            let arr = pop_val_exn self |> Value.to_array_exn in
            Vec.clear arr
          | Tforce ->
            let th = pop_val_exn self |> Value.to_thunk_exn in
            (match Thunk.state th with
            | Th_err err -> raise (Error.E err)
            | Th_ok vs -> push_vals self vs
            | Th_lazy c ->
              self.ip <- ip;
              (* suspend *)
              raise (Suspend_and_eval_chunk (th, c))
            | Th_suspended { c; vm } ->
              self.ip <- ip;
              (* suspend *)
              raise (Suspend_and_resume (th, c, vm)))
          | Curch ->
            (* push [c] onto the stack *)
            push_val self (Value.chunk c)
          | Type -> push_val self (Value.expr @@ K.Expr.type_ self.ctx)
          | Tyarr ->
            let b = pop_val_exn self |> Value.to_expr_exn in
            let a = pop_val_exn self |> Value.to_expr_exn in
            push_val self (Value.expr @@ K.Expr.arrow self.ctx a b)
          | Var ->
            let ty = pop_val_exn self |> Value.to_expr_exn in
            let str = pop_val_exn self |> Value.to_str_exn in
            let v = K.Var.make str ty in
            push_val self (Value.var v)
          | Vty ->
            let v = pop_val_exn self |> Value.to_var_exn in
            push_val self (Value.expr @@ K.Var.ty v)
          | Evar ->
            let v = pop_val_exn self |> Value.to_var_exn in
            let e = K.Expr.var self.ctx v in
            push_val self (Value.expr e)
          | Eapp ->
            let arg = pop_val_exn self |> Value.to_expr_exn in
            let f = pop_val_exn self |> Value.to_expr_exn in
            let e = K.Expr.app self.ctx f arg in
            push_val self (Value.expr e)
          | Elam ->
            let bod = pop_val_exn self |> Value.to_expr_exn in
            let v = pop_val_exn self |> Value.to_var_exn in
            let e = K.Expr.lambda self.ctx v bod in
            push_val self (Value.expr e)
          | Econst ->
            let args =
              pop_val_exn self |> Value.to_array_exn |> Vec.to_list
              |> List.map Value.to_expr_exn
            in
            let c = pop_val_exn self |> Value.to_const_exn in
            let e = K.Expr.const self.ctx c args in
            push_val self (Value.expr e)
          | Econst0 ->
            let c = pop_val_exn self |> Value.to_const_exn in
            let e = K.Expr.const self.ctx c [] in
            push_val self (Value.expr e)
          | Econst1 ->
            let ty0 = pop_val_exn self |> Value.to_expr_exn in
            let c = pop_val_exn self |> Value.to_const_exn in
            let e = K.Expr.const self.ctx c [ ty0 ] in
            push_val self (Value.expr e)
          | Suem -> push_val self (Value.subst K.Subst.empty)
          | Subinde ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            let v = pop_val_exn self |> Value.to_var_exn in
            let su = pop_val_exn self |> Value.to_subst_exn in
            push_val self @@ Value.subst (K.Subst.bind su v e)
          | Subindty ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            let v = pop_val_exn self |> Value.to_var_exn in
            let su = pop_val_exn self |> Value.to_subst_exn in
            push_val self @@ Value.subst (K.Subst.bind su v e)
          | Devar ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            (match K.Expr.view e with
            | K.E_var v ->
              push_val self (Value.var v);
              push_val self Value.true_
            | _ ->
              push_val self Value.nil;
              push_val self Value.false_)
          | Deapp ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            (match K.Expr.view e with
            | K.E_app (f, a) ->
              push_val self (Value.expr f);
              push_val self (Value.expr a);
              push_val self Value.true_
            | _ ->
              push_val self Value.nil;
              push_val self Value.nil;
              push_val self Value.false_)
          | Delam ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            (match K.Expr.view e with
            | K.E_lam _ ->
              let v, bod = K.Expr.open_lambda_exn self.ctx e in
              push_val self (Value.var v);
              push_val self (Value.expr bod);
              push_val self Value.true_
            | _ ->
              push_val self Value.nil;
              push_val self Value.nil;
              push_val self Value.false_)
          | Deconst ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            (match K.Expr.view e with
            | K.E_const (c, args) ->
              push_val self (Value.const c);
              let args = args |> List.map Value.expr |> Vec.of_list in
              push_val self (Value.array args);
              push_val self Value.true_
            | _ ->
              push_val self Value.nil;
              push_val self Value.nil;
              push_val self Value.false_)
          | Thabs ->
            let v = pop_val_exn self |> Value.to_var_exn in
            let th = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.abs self.ctx v th in
            push_val self (Value.thm th)
          | Thcongr ->
            let th2 = pop_val_exn self |> Value.to_thm_exn in
            let th1 = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.congr self.ctx th1 th2 in
            push_val self (Value.thm th)
          | Thass ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            let th = K.Thm.assume self.ctx e in
            push_val self (Value.thm th)
          | Thcut ->
            let th2 = pop_val_exn self |> Value.to_thm_exn in
            let th1 = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.cut self.ctx th1 th2 in
            push_val self (Value.thm th)
          | Threfl ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            let th = K.Thm.refl self.ctx e in
            push_val self (Value.thm th)
          | Thsym ->
            let th = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.sym self.ctx th in
            push_val self (Value.thm th)
          | Thtrans ->
            let th2 = pop_val_exn self |> Value.to_thm_exn in
            let th1 = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.trans self.ctx th1 th2 in
            push_val self (Value.thm th)
          | Thbeq ->
            let th2 = pop_val_exn self |> Value.to_thm_exn in
            let th1 = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.bool_eq self.ctx th1 th2 in
            push_val self (Value.thm th)
          | Thbeqi ->
            let th2 = pop_val_exn self |> Value.to_thm_exn in
            let th1 = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.bool_eq_intro self.ctx th1 th2 in
            push_val self (Value.thm th)
          | Thbeta ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            let th = K.Thm.beta_conv self.ctx e in
            push_val self (Value.thm th)
          | Thsubst ->
            let su = pop_val_exn self |> Value.to_subst_exn in
            let th = pop_val_exn self |> Value.to_thm_exn in
            let th = K.Thm.subst ~recursive:false self.ctx th su in
            push_val self (Value.thm th)
          | Dth ->
            let th = pop_val_exn self |> Value.to_thm_exn in
            let hyps =
              K.Thm.hyps_sorted_l th |> List.map Value.expr |> Vec.of_list
            in
            push_val self (Value.array hyps);
            let concl = K.Thm.concl th in
            push_val self (Value.expr concl)
          | Stopexec -> raise Stop_exec
        )
      done
    with Stop_exec -> ()
end

(* chunk builder. temporary structure to construct chunks. *)
module Chunk_builder = struct
  open Types_

  type t = {
    cb_instrs: instr Vec.t;  (** Instructions *)
    mutable cb_n_regs: int;  (** Number of regs to allocate for this chunk *)
    cb_locals: value Vec.t;  (** Local values, used by some instructions *)
    cb_n_args: int;
    cb_n_ret: int;
    cb_comments: (int * string) Vec.t;
    cb_allow_comments: bool;
  }

  let create ?(allow_comments = true) ~n_args ~n_ret () : t =
    {
      cb_instrs = Vec.create ();
      cb_n_regs = 0;
      cb_locals = Vec.create ();
      cb_comments = Vec.create ();
      cb_n_args = n_args;
      cb_n_ret = n_ret;
      cb_allow_comments = allow_comments;
    }

  let reset (self : t) : unit =
    let { cb_instrs; cb_locals; cb_n_regs = _ } = self in
    self.cb_n_regs <- 0;
    Vec.clear cb_instrs;
    Vec.clear cb_locals;
    ()

  let to_chunk (self : t) : chunk =
    {
      c_instrs = Vec.to_array self.cb_instrs;
      c_n_regs = self.cb_n_regs;
      c_n_args = self.cb_n_args;
      c_n_ret = self.cb_n_ret;
      c_locals = Vec.to_array self.cb_locals;
      c_comments = Vec.to_array self.cb_comments;
    }

  exception L_found of int

  let[@inline] add_local (self : t) (v : value) : int =
    match
      (* look for [v] in the existing locals *)
      Vec.iteri
        (fun i v' -> if Value.equal v v' then raise (L_found i))
        self.cb_locals;
      ()
    with
    | exception L_found i -> i
    | () ->
      let i = Vec.size self.cb_locals in
      Vec.push self.cb_locals v;
      i

  let push_comment self str =
    if self.cb_allow_comments then (
      let i = Vec.size self.cb_instrs in
      Vec.push self.cb_comments (i, str)
    )

  let push_i self (i : instr) : unit =
    Vec.push self.cb_instrs i;
    match i with
    | Rstore i | Rload i -> self.cb_n_regs <- max (i + 1) self.cb_n_regs
    | _ -> ()

  (* current position in the list of instructions *)
  let cur_pos (self : t) : int = Vec.size self.cb_instrs

  (* set an instruction after the fact *)
  let set_i (self : t) i (instr : instr) : unit =
    assert (i < Vec.size self.cb_instrs);
    Vec.set self.cb_instrs i instr
end

type t = Types_.vm

type debug_hook = t -> Instr.t -> unit

let set_debug_hook vm h = vm.Types_.debug_hook <- Some h

let clear_debug_hook vm = vm.Types_.debug_hook <- None

let dump = VM_.dump

let create ~ctx () : t =
  let vm = VM_.create ~ctx in
  vm

let reset = VM_.reset

let push = VM_.push_val

let pop = VM_.pop_val

let pop_exn = VM_.pop_val_exn

let run self c =
  VM_.enter_chunk self c ~n:0;
  VM_.run self

let eval_thunk ?debug_hook (ctx : K.Ctx.t) (th : Thunk.t) :
    (Value.t list, Error.t) result =
  let open Types_ in
  let open struct
    type eval_task =
      | Eval_thunk of thunk
      | Eval_chunk of thunk * chunk * vm
  end in
  let vms = Vec.create () in

  (* can be reused *)
  let[@inline] recycle_vm_ vm =
    VM_.reset vm;
    Vec.push vms vm
  in
  let[@inline] alloc_vm () =
    let vm =
      match Vec.pop vms with
      | Some vm -> vm
      | None -> VM_.create ~ctx
    in
    Option.iter (set_debug_hook vm) debug_hook;
    vm
  in

  let stack : eval_task Vec.t = Vec.create () in

  Vec.push stack (Eval_thunk th);

  let eval_chunk ~th ~vm ~c : unit =
    match
      VM_.enter_chunk vm c ~n:0;
      VM_.run vm;
      VM_.pop_vals vm
    with
    | vs ->
      recycle_vm_ vm;
      th.th_st <- Th_ok vs
    | exception Error.E err ->
      recycle_vm_ vm;
      th.th_st <- Th_err err
    | exception Suspend_and_eval_chunk (th', c') ->
      (* park [c] *)
      Vec.push stack (Eval_chunk (th, c, vm));
      (* eval [c'] first *)
      Vec.push stack (Eval_chunk (th', c', alloc_vm ()))
    | exception Suspend_and_resume (th', c', vm') ->
      (* park [c] *)
      Vec.push stack (Eval_chunk (th, c, vm));
      (* resume evaluation of [c'] first in [vm'] *)
      Vec.push stack (Eval_chunk (th', c', vm'))
  in

  while not (Vec.is_empty stack) do
    let task = Vec.pop_exn stack in
    match task with
    | Eval_chunk (th, c, vm) -> eval_chunk ~th ~vm ~c
    | Eval_thunk th ->
      (match Thunk.state th with
      | Th_ok _ | Th_err _ -> ()
      | Th_lazy c ->
        let vm = alloc_vm () in
        eval_chunk ~th ~c ~vm
      | Th_suspended { c; vm } -> eval_chunk ~th ~c ~vm)
  done;
  Thunk.get_result_exn th

let eval_thunk1 ?debug_hook ctx th : _ result =
  match eval_thunk ?debug_hook ctx th with
  | Ok [ v ] -> Ok v
  | Ok vs ->
    Error
      (Error.makef "eval_thunk1: expected one result, got %d" (List.length vs))
  | Error _ as e -> e

module Eval_effect = struct
  type t =
    | Eff_declare of string * K.ty
    | Eff_define of string * K.Expr.t
    | Eff_print_val of Value.t
    | Eff_prove of string * K.Sequent.t * K.Thm.t Error.or_error
    | Eff_define_thunk of string * thunk
    | Eff_define_chunk of string * chunk
    | Eff_print_error of Error.t

  let pp_res out = function
    | Ok vs ->
      List.iteri
        (fun i v ->
          if i > 0 then Fmt.fprintf out "@ ";
          Value.pp out v)
        vs
    | Error err -> Fmt.fprintf out "error: %a" Error.pp err

  and pp_res1 ppx out = function
    | Ok v -> Fmt.fprintf out "result: %a" ppx v
    | Error err -> Fmt.fprintf out "error: %a" Error.pp err

  let pp out = function
    | Eff_declare (name, ty) ->
      Fmt.fprintf out "(@[declare %s :@ %a@])" name K.Expr.pp ty
    | Eff_define (name, body) ->
      Fmt.fprintf out "(@[define %s :=@ %a@])" name K.Expr.pp body
    | Eff_print_val v -> Fmt.fprintf out "(@[<v2>eval:@ %a@])" Value.pp v
    | Eff_prove (name, goal, proof) ->
      Fmt.printf "(@[proof %s@ :goal %a@ :proof %a@])" name K.Sequent.pp goal
        (pp_res1 K.Thm.pp) proof
    | Eff_define_thunk (name, th) ->
      Fmt.fprintf out "(@[def %s =@ %a@])" name Thunk.pp th
    | Eff_define_chunk (name, c) ->
      Fmt.fprintf out "(@[def %s =@ %a@])" name Chunk.pp c
    | Eff_print_error err -> Fmt.fprintf out "(@[err@ %a@])" Error.pp err
end

let unwrap_ = function
  | Ok v -> v
  | Error err -> Error.raise err

let eval_stanza ?debug_hook (ctx : K.Ctx.t) (stanza : Stanza.t) : _ list =
  let module Eff = Eval_effect in
  try
    match Stanza.view stanza with
    | Stanza.Declare { name; ty } ->
      let ty = eval_thunk1 ?debug_hook ctx ty |> unwrap_ |> Value.to_expr_exn in
      [ Eff.Eff_declare (name, ty) ]
    | Stanza.Define { name; body } ->
      let body =
        eval_thunk1 ?debug_hook ctx body |> unwrap_ |> Value.to_expr_exn
      in
      [ Eff.Eff_define (name, body) ]
    | Stanza.Prove { name; goal; proof } ->
      let goal =
        eval_thunk1 ?debug_hook ctx goal |> unwrap_ |> Value.to_seq_exn
      in
      let proof =
        eval_thunk1 ?debug_hook ctx proof |> Result.map Value.to_thm_exn
      in
      [ Eff.Eff_prove (name, goal, proof) ]
    | Stanza.Define_thunk { name; value } ->
      [ Eff.Eff_define_thunk (name, value) ]
    | Stanza.Define_chunk { name; value } ->
      [ Eff.Eff_define_chunk (name, value) ]
    | Stanza.Eval { value } ->
      let r = eval_thunk ?debug_hook ctx value in
      (match r with
      | Ok l -> List.map (fun v -> Eff.Eff_print_val v) l
      | Error e -> [ Eff.Eff_print_error e ])
  with Error.E err -> [ Eff.Eff_print_error err ]

let eval_stanza_pp ?debug_hook ctx stanza : unit =
  let l = eval_stanza ?debug_hook ctx stanza in
  List.iter (Fmt.printf "%a@." Eval_effect.pp) l
