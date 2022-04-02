
open Sigs
module K = Kernel

type 'a vec = 'a Vec.t
let[@inline] (let@) f x = f x

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

    call_prim: primitive Vec.t;
    (** Primitives currently being evaluated *)

    regs: value Vec.t;
    (** Stack of register value. Each call frame has its own
        local register. *)

    ctx: K.Ctx.t;
    (** Logical context *)

    mutable debug_hook: (vm -> instr -> unit) option;
  }

  and thunk = {
    mutable th_st: thunk_state
  }

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
    | Const of K.Const.t
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

  and instr = thunk VM_instr_.t

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
    | Const x -> K.Const.pp out x
    | Subst x -> K.Subst.pp out x
    | Theory x -> K.Theory.pp out x
    | Chunk c ->
      if short then Fmt.string out "<chunk>" else pp_chunk out c
    | Prim p -> pp_prim out p

  and pp_thunk_state out = function
    | Th_ok v ->
      Fmt.fprintf out "(@[ok %a@])" (pp_list @@ pp_value ~short:true) v
    | Th_err e -> Fmt.fprintf out "(@[err %a@])" Error.pp e
    | Th_lazy _ -> Fmt.string out "(lazy)"
    | Th_suspended _c -> Fmt.string out "(suspended)"

  and pp_thunk out (self:thunk) =
    Fmt.fprintf out "(@[thunk@ :st %a@])" pp_thunk_state self.th_st

  and pp_chunk ?ip out (self:chunk) : unit =
    let pp_instr out i =
      VM_instr_.pp pp_thunk out i;
      begin match i with
        | Lload n ->
          let local = self.c_locals.(n) in
          Fmt.fprintf out " ; %a" (pp_value ~short:true) local
        | _ -> ()
      end
    in
    let ppi pre ppx out (i,x) =
      Fmt.fprintf out "%s%-8d %a" pre i ppx x in
    let ppi_ip ppx out (i,x) =
      let ptr = match ip with Some i' when i=i' -> ">" | _ -> " " in
      ppi ptr ppx out (i,x) in
    Fmt.fprintf out "@[<v2>chunk[%d regs] {@ :instrs@ %a@ :locals@ %a@;<1 -2>}@]"
      self.c_n_regs
      (pp_arri ~sep:"" @@ ppi_ip pp_instr) self.c_instrs
      (pp_arri ~sep:"" @@ ppi " " @@ pp_value ~short:false) self.c_locals

  and pp_prim out (p:primitive) : unit =
    Fmt.fprintf out "<prim %s>" p.pr_name
end

type vm = Types_.vm
type thunk = Types_.thunk

(* auto generated instructions *)
module Instr = struct
  open Types_
  type t = instr

  let pp = VM_instr_.pp pp_thunk
  let to_string = Fmt.to_string pp
end

module Value = struct
  open Types_
  type t = value

  let nil : t = Nil
  let bool b : t = Bool b
  let true_ = bool true
  let false_ = bool false
  let int (x:int) : t = Int x
  let string (x:string) : t = String x
  let array (x:t vec) : t = Array x
  let expr (x:K.Expr.t) : t = Expr x
  let thm (x:K.Thm.t) : t = Thm x
  let var (x:K.Var.t) : t = Var x
  let const (x:K.Const.t) : t = Const x
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
    | Const c1, Const c2 -> K.Const.equal c1 c2
    | Subst s1, Subst s2 -> K.Subst.equal s1 s2
    | Theory th1, Theory th2 -> th1 == th2
    | Chunk c1, Chunk c2 -> c1 == c2
    | Prim p1, Prim p2 -> p1.pr_name = p2.pr_name
    | (Bool _ | Int _ | String _ | Array _ | Const _
      | Expr _ | Thm _ | Var _ | Subst _ |
       Theory _ | Nil | Chunk _ | Prim _), _ -> false


  type 'a conv_to = t -> 'a option
  type 'a conv_to_exn = t -> 'a

  let[@inline] to_str = function String x -> Some x | _ -> None
  let[@inline] to_bool = function Bool x -> Some x | _ -> None
  let[@inline] to_int = function Int x -> Some x | _ -> None
  let[@inline] to_expr = function Expr x -> Some x | _ -> None
  let[@inline] to_thm = function Thm x -> Some x | _ -> None
  let[@inline] to_var = function Var x -> Some x | _ -> None
  let[@inline] to_const = function Const x -> Some x | _ -> None
  let[@inline] to_array = function Array x -> Some x | _ -> None
  let[@inline] to_subst = function Subst x -> Some x | _ -> None

  let[@inline] to_str_exn = function String x -> x | _ -> Error.fail "expected string"
  let[@inline] to_bool_exn = function Bool x -> x | _ -> Error.fail "expected bool"
  let[@inline] to_int_exn = function Int x -> x | _ -> Error.fail "expected int"
  let[@inline] to_expr_exn = function Expr x -> x | _ -> Error.fail "expected expr"
  let[@inline] to_thm_exn = function Thm x -> x | _ -> Error.fail "expected thm"
  let[@inline] to_var_exn = function Var x -> x | _ -> Error.fail "expected var"
  let[@inline] to_const_exn = function Const x -> x | _ -> Error.fail "expected const"
  let[@inline] to_array_exn = function Array x -> x | _ -> Error.fail "expected array"
  let[@inline] to_subst_exn = function Subst x -> x | _ -> Error.fail "expected subst"
end

module Chunk = struct
  open Types_
  type t = chunk
  let pp out c = pp_chunk out c
  let to_string = Fmt.to_string pp
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
  let to_string = Fmt.to_string pp
  let make ~name ~eval () : t =
    { pr_name=name; pr_eval=eval; }
end

module Thunk = struct
  open Types_
  type t = thunk

  let[@inline] state self = self.th_st
  let resolved self = match state self with
    | Th_ok _ | Th_err _ -> true
    | Th_lazy _ | Th_suspended _ -> false

  let get_result_exn self = match state self with
    | Th_ok v -> Stdlib.Ok v
    | Th_err e -> Stdlib.Error e
    | Th_suspended _ | Th_lazy _ -> assert false

  let pp_state = pp_thunk_state
  let pp = pp_thunk
  let to_string = Fmt.to_string pp

  let make c : t = {th_st=Th_lazy c}
end

(* TODO: remove
(* a stack used to evaluate thunks on demand *)
module Eval_stack_ : sig
  type t
  val create : unit -> t
  val is_empty : t -> bool
  val push : t -> Thunk.t -> unit
  val pop_exn : t -> Thunk.t
  val size : t -> int
  val pp : t Fmt.printer
end = struct
  type t = {
    stack: Thunk.t Vec.t;
  }

  let create() : t = {stack=Vec.create()}
  let is_empty self = Vec.is_empty self.stack
  let push self x = Vec.push self.stack x
  let pop_exn self = Vec.pop_exn self.stack
  let size self = Vec.size self.stack
  let pp out (self:t) =
    Fmt.fprintf out "(@[eval-stack@ [@[%a@]]@])"
      (pp_iter Thunk.pp) (Vec.to_iter self.stack)
end
   *)

module Stanza = struct
  type view =
    | Declare of {
        name: Name.t;
        ty: Thunk.t;
      }

    | Define of {
        name: Name.t;
        body: Thunk.t;
      }

    | Prove of {
        name: Name.t;
        deps: (Name.t * [`Eager | `Lazy] * string) list;
        goal: Thunk.t; (* sequent *)
        proof: Thunk.t; (* thm *)
      }

    | Define_meta of {
        name: string;
        value: Thunk.t;
      } (** Define a meta-level value *)

    | Eval_meta of {
        value: Thunk.t;
      }

  type t = {
    id: Sym_ptr.t;
    view: view;
  }

  let[@inline] view self = self.view
  let[@inline] make ~id view : t = {view; id}
  let[@inline] id self = self.id

  let pp out (self:t) : unit =
    match view self with
    | Declare {name; ty} ->
      Fmt.fprintf out "(@[declare %a@ :ty %a@])" Name.pp name Thunk.pp ty
    | Define {name; body} ->
      Fmt.fprintf out "(@[define %a@ :body %a@])" Name.pp name Thunk.pp body
    | Define_meta {name; value} ->
      Fmt.fprintf out "(@[def `%s`@ :chunk %a@])"
        name Thunk.pp value
    | Prove {name; deps; goal; proof} ->
      let pp_dep out (s,kind,ref) =
        let skind = match kind with `Eager -> ":eager" | `Lazy -> ":lazy" in
        Fmt.fprintf out "(@[%a %s %s@ :goal %a@ :proof %a@])"
          Name.pp s skind ref Thunk.pp goal Thunk.pp proof
      in
      Fmt.fprintf out "(@[prove %a@ :deps (@[%a@])@])"
        Name.pp name (pp_list pp_dep) deps
    | Eval_meta {value} ->
      Fmt.fprintf out "(@[eval@ %a@])" Thunk.pp value
end

module Scoping_env = struct
  open Types_

  type entry =
    | E_th of thunk
    | E_prove of {
        goal: thunk;
        proof: thunk;
      }
    | E_define of { body: thunk }
    | E_declare of { ty: thunk }

  type t = {
    entries: entry Str_map.t;
  } [@@unboxed]

  let empty : t = {
    entries=Str_map.empty;
  }

  let pp_entry out = function
    | E_th t -> Fmt.fprintf out "(@[thunk@ %a@])" Thunk.pp t
    | E_prove {goal;proof} ->
      Fmt.fprintf out "(@[prove@ :goal %a@ :proof %a@])" Thunk.pp goal Thunk.pp proof
    | E_define {body} ->
      Fmt.fprintf out "(@[define@ :body %a@])" Thunk.pp body
    | E_declare {ty} ->
      Fmt.fprintf out "(@[declare@ :ty %a@])" Thunk.pp ty

  let pp out (self:t) =
    let pp_pair out (s,v) =
      Fmt.fprintf out "@[%s := %a@]" s pp_entry v in
    Fmt.fprintf out
      "(@[env@ %a@])"
      (pp_iter ~sep:";" pp_pair) (Str_map.to_iter self.entries)

  let[@inline] mk_ entries : t = {entries}
  let[@inline] mem k self = Str_map.mem k self.entries
  let[@inline] add s v self : t = mk_ @@ Str_map.add s v self.entries
  let[@inline] find s self = Str_map.find_opt s self.entries
  let[@inline] get self s = Str_map.find_opt s self.entries
  let[@inline] iter self = Str_map.to_iter self.entries

  let add_proof_dep (self:t) (name, kind, ref) : t =
    match find ref self with
    | Some (E_prove {goal; proof}) ->
      (* pick which thunk we want *)
      let th = match kind with
        | `Eager -> proof
        | `Lazy ->
          (* FIXME: make a thunk that boxes this *)
          goal
      in
      add (Name.to_string name) (E_th th) self
    | Some _ -> Error.failf (fun k->k"expected %S to be a prove step" ref)
    | None -> Error.failf (fun k->k"cannot find prove step %S in env" ref)

  let add_proof_deps self l = List.fold_left add_proof_dep self l

  let add_stanza (stanza:Stanza.t) (self:t) : t =
    match Stanza.view stanza with
    | Stanza.Define_meta {name;value} ->
      add name (E_th value) self
    | Stanza.Eval_meta _ -> self
    | Stanza.Define {name; body} ->
      add (Name.to_string name) (E_define {body}) self
    | Stanza.Prove {name; deps=_; goal; proof} ->
      add (Name.to_string name) (E_prove {goal;proof}) self
    | Stanza.Declare {name; ty} ->
      add (Name.to_string name) (E_declare {ty}) self
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

  let create ~ctx : t = {
    stack=Vec.make 128 Value.nil;
    call_stack=Vec.make 12 Chunk.dummy;
    call_restore_ip=Vec.make 12 0;
    call_prim=Vec.create ();
    ip=0;
    regs=Vec.make 32 Value.nil;
    ctx;
    debug_hook=None;
  }

  let[@inline] push_val (self:t) v = Vec.push self.stack v

  let push_vals (self:t) l = List.iter (Vec.push self.stack) l

  let[@inline] pop_val (self:t) = Vec.pop self.stack

  let[@inline] pop_val_exn (self:t) : Value.t =
    if Vec.is_empty self.stack then (
      Error.fail"vm.pop: operand stack is empty";
    );
    Vec.pop_exn self.stack

  let pop_vals (self:t) : Value.t list =
    let l = Vec.to_list self.stack in
    Vec.clear self.stack;
    l

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
          call_restore_ip; regs; debug_hook=_; } = self in
    self.ip <- 0;
    Vec.clear self.call_stack;
    Vec.clear self.call_restore_ip;
    Vec.clear stack;
    Vec.clear self.call_prim;
    Vec.clear regs;
    self.debug_hook <- None;
    ()

  let enter_chunk (self:t) (c:chunk) : unit =
    if not (Vec.is_empty self.call_stack) then (
      Vec.push self.call_restore_ip self.ip;
    );
    Vec.push self.call_stack c;
    self.ip <- 0;
    (* allocate regs for [c] *)
    for _j = 1 to c.c_n_regs do
      Vec.push self.regs Value.nil
    done

  let pop_chunk (self:t) : unit =
    let c = Vec.pop_exn self.call_stack in
    if c.c_n_regs > 0 then (
      Vec.shrink self.regs (Vec.size self.regs - c.c_n_regs);
    );
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
    Vec.get self.regs (Vec.size self.regs - n + i)

  let rstore (self:t) (i:int) v : unit =
    let c = Vec.last_exn self.call_stack in
    let n = c.c_n_regs in
    if i >= n then Error.fail "vm.rstore: not enough registers";
    Vec.set self.regs (Vec.size self.regs - n + i) v

  let dump out (self:t) : unit =
    let {
      stack; call_stack; ip; call_restore_ip;
      call_prim;
      regs; } = self in
    Fmt.fprintf out "@[<v2>VM {@ ";
    Fmt.fprintf out "@[call stack: %d frames@]" (Vec.size call_stack);
    if not (Vec.is_empty call_stack) then (
      let c = Vec.last_exn call_stack in
      Fmt.fprintf out "@,@[<v2>top chunk: {@ ";
      Chunk.pp_at ~ip out c;

      (* print registers *)
      if c.c_n_regs > 0 then (
        for i=0 to c.c_n_regs-1 do
          let v = Vec.get self.regs (Vec.size self.regs - c.c_n_regs + i) in
          Fmt.fprintf out "@,reg[%d]: %a" i Value.pp_short v;
        done;
      );

      Fmt.fprintf out "@;<1 -2>}@]";
    );

    if Vec.is_empty self.stack then (
      Fmt.fprintf out "@,operand stack: []"
    ) else (
      Fmt.fprintf out "@,@[<v2>operand stack: [@ ";
      Vec.iteri (fun i v ->
          if i>0 then Fmt.fprintf out "@,";
          Fmt.fprintf out "[%d]: %a" i Value.pp_short v)
        stack;
      Fmt.fprintf out "@;<1 -2>]@]";
    );

    Fmt.fprintf out "@;<1 -2>}@]"

  let run (self:t) : unit =
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

          begin match self.debug_hook with
            | None -> ()
            | Some h -> h self instr;
          end;

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
            let b = pop_val_exn self |> Value.to_int_exn in
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a+b))

          | Add1 ->
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a+1))

          | Sub ->
            let b = pop_val_exn self |> Value.to_int_exn in
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a-b))

          | Sub1 ->
            let a = pop_val_exn self |> Value.to_int_exn in
            push_val self (Value.int (a-1))

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
            if x then self.ip <- ip;

          | Jifn ip ->
            let x = pop_val_exn self |> Value.to_bool_exn in
            if not x then self.ip <- ip;

          | Jmp ip ->
            self.ip <- ip

          | Tforce th ->
            begin match Thunk.state th with
              | Th_err err -> raise (Error.E err)
              | Th_ok vs ->
                push_vals self vs;

              | Th_lazy c ->
                self.ip <- ip; (* suspend *)
                raise (Suspend_and_eval_chunk (th,c))

              | Th_suspended {c;vm} ->
                self.ip <- ip; (* suspend *)
                raise (Suspend_and_resume (th,c,vm))

            end;

          | Curch ->
            (* push [c] onto the stack *)
            push_val self (Value.chunk c);

          | Type ->
            push_val self (Value.expr @@ K.Expr.type_ self.ctx)

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
            push_val self (Value.expr @@ K.Var.ty v);

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
              pop_val_exn self |> Value.to_array_exn
              |> Vec.to_list
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
            let e = K.Expr.const self.ctx c [ty0] in
            push_val self (Value.expr e)

          | Devar ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            begin match K.Expr.view e with
              | K.E_var v ->
                push_val self (Value.var v);
                push_val self Value.true_;
              | _ ->
                push_val self Value.nil;
                push_val self Value.false_;
            end;

          | Deapp ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            begin match K.Expr.view e with
              | K.E_app (f,a) ->
                push_val self (Value.expr f);
                push_val self (Value.expr a);
                push_val self Value.true_;
              | _ ->
                push_val self Value.nil;
                push_val self Value.nil;
                push_val self Value.false_;
            end;

          | Delam ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            begin match K.Expr.view e with
              | K.E_lam _ ->
                let v, bod = K.Expr.open_lambda_exn self.ctx e in
                push_val self (Value.var v);
                push_val self (Value.expr bod);
                push_val self Value.true_;
              | _ ->
                push_val self Value.nil;
                push_val self Value.nil;
                push_val self Value.false_;
            end;

          | Deconst ->
            let e = pop_val_exn self |> Value.to_expr_exn in
            begin match K.Expr.view e with
              | K.E_const (c,args) ->
                push_val self (Value.const c);
                let args = args |> List.map Value.expr |> Vec.of_list in
                push_val self (Value.array args);
                push_val self Value.true_;
              | _ ->
                push_val self Value.nil;
                push_val self Value.nil;
                push_val self Value.false_;
            end;

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

          | Dth ->
            let th = pop_val_exn self |> Value.to_thm_exn in
            let hyps =
              K.Thm.hyps_sorted_l th |> List.map Value.expr |> Vec.of_list in
            push_val self (Value.array hyps);
            let concl = K.Thm.concl th in
            push_val self (Value.expr concl);
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
      | _ -> ()
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
    { str; prims; }

  type st = {
    mutable tok: VM_lex.token;
    mutable env: Scoping_env.t;
    buf: Lexing.lexbuf;
    prims: Primitive.t Str_map.t;
    cb: CB.t;
    mutable n : int; (* to give IDs *)
    delayed: (unit -> unit) Vec.t; (* set instructions based on labels *)
    mutable labels: int Str_map.t; (* offset of labels *)
  }

  let create_st ?tok prims buf ~env : st =
    let tok = match tok with
      | Some t -> t
      | None -> VM_lex.token buf
    in
    { tok;
      buf;
      env;
      prims;
      cb = CB.create();
      n = 0;
      delayed=Vec.create();
      labels=Str_map.empty;
    }

  let new_pos_id_ (self:st) : Sym_ptr.t =
    let id = Sym_ptr.pos self.n in
    self.n <- self.n + 1;
    id

  (* consume current token *)
  let consume (self:st) : unit =
    (*Format.eprintf "consume %a@." VM_lex.pp_tok self.tok;*)
    self.tok <- VM_lex.token self.buf

  let exact (self:st) what tok =
    let tok' = self.tok in
    if tok <> tok' then Error.failf (fun k->k"expected %s" what);
    consume self

  let lparen self = exact self "'('" VM_lex.LPAREN
  let rparen self = exact self "')'" VM_lex.RPAREN
  let rbrace self = exact self "'}'" VM_lex.RBRACE

  let int (self:st) = match self.tok with
    | VM_lex.INT i -> consume self; int_of_string i
    | _ -> Error.fail "expected integer"

  let quoted_str (self:st) = match self.tok with
    | VM_lex.QUOTED_STR s -> consume self; s
    | _ -> Error.fail "expected quoted string"

  let list_of ~p (self:st) = match self.tok with
    | VM_lex.LPAREN ->
      consume self;
      let rec loop acc = match self.tok with
        | VM_lex.RPAREN ->
          consume self; List.rev acc
        | _ ->
          let x = p self in loop (x::acc)
      in
      loop []
    | _ -> Error.fail "expected a list"

  let atom self = match self.tok with
    | VM_lex.ATOM s -> consume self; s
    | _ -> Error.fail "expected atom"

  let colon_str self = match self.tok with
    | VM_lex.COLON_STR s -> consume self; s
    | _ -> Error.fail "expected label (e.g. `:foo`)"

  (** Parse a chunk into [self.cb] *)
  let rec parse_chunk_into_ (self:st) : unit =
    let module I = VM_instr_ in
    let[@inline] recurse() = parse_chunk_into_ self in

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

    match self.tok with
    | VM_lex.QUOTED_STR s ->
      consume self;
      let n = CB.add_local self.cb (Value.string s) in
      CB.add_instr self.cb (I.Lload n);
      recurse()

    | VM_lex.COLON_STR lbl ->
      consume self;
      (* remember position of label *)
      self.labels <- Str_map.add lbl (CB.cur_pos self.cb) self.labels;
      recurse();

    | VM_lex.LPAREN ->
      consume self;
      let str = atom self in
      begin match str with
        | "extract" ->
          let i = int self in
          rparen self;
          CB.add_instr self.cb (I.Extract i)

        | "rstore" ->
          let i = int self in
          rparen self;
          CB.add_instr self.cb (I.Rstore i)

        | "rload" ->
          let i = int self in
          rparen self;
          CB.add_instr self.cb (I.Rload i)

        | "lload" ->
          let i = int self in
          rparen self;
          CB.add_instr self.cb (I.Lload i)

        | "tforce" ->
          let name = quoted_str self in
          rparen self;
          begin match Scoping_env.find name self.env with
            | Some (Scoping_env.E_th th) ->
              (* evaluate thunk lazily *)
              CB.add_instr self.cb (I.Tforce th)
            | Some _ ->
              Error.failf (fun k->k"tforce: expected a thunk for %S" name)
            | None ->
              Error.failf (fun k->k"tforce: cannot find %S in environment" name)
          end

        | "jif" ->
          let lbl = colon_str self in
          rparen self;
          let cur_pos = CB.cur_pos self.cb in
          CB.add_instr self.cb I.Nop;
          with_label lbl (fun lbl_pos ->
              CB.set_instr self.cb cur_pos (I.Jif lbl_pos))

        | "jifn" ->
          let lbl = colon_str self in
          rparen self;
          let cur_pos = CB.cur_pos self.cb in
          CB.add_instr self.cb I.Nop;
          with_label lbl (fun lbl_pos ->
              CB.set_instr self.cb cur_pos (I.Jifn lbl_pos))

        | "jmp" ->
          let lbl = colon_str self in
          rparen self;
          let cur_pos = CB.cur_pos self.cb in
          CB.add_instr self.cb I.Nop;
          with_label lbl (fun lbl_pos ->
              CB.set_instr self.cb cur_pos (I.Jmp lbl_pos))

        | _ ->
          Error.failf (fun k->k"invalid instruction %S" str)
      end;
      recurse ()

    | VM_lex.LBRACKET -> Error.fail "syntax error"
    | VM_lex.RBRACKET -> Error.fail "syntax error"
    | VM_lex.LANGLE -> Error.fail "syntax error"
    | VM_lex.RANGLE -> Error.fail "syntax error"

    | VM_lex.INT i ->
      consume self;
      let i = int_of_string i in
      CB.add_instr self.cb (I.Int i);
      recurse()

    | VM_lex.ATOM str ->
      consume self;
      begin match str with
        | "nop" -> CB.add_instr self.cb I.Nop
        | "call" -> CB.add_instr self.cb I.Call
        | "ret" -> CB.add_instr self.cb I.Ret
        | "dup" -> CB.add_instr self.cb I.Dup
        | "drop" -> CB.add_instr self.cb I.Drop
        | "exch" -> CB.add_instr self.cb I.Exch
        | "true" -> CB.add_instr self.cb (I.Bool true)
        | "false" -> CB.add_instr self.cb (I.Bool false)
        | "nil" -> CB.add_instr self.cb I.Nil
        | "not" ->  CB.add_instr self.cb I.Not
        | "add" -> CB.add_instr self.cb I.Add
        | "add1" -> CB.add_instr self.cb I.Add1
        | "sub" -> CB.add_instr self.cb I.Sub
        | "sub1" -> CB.add_instr self.cb I.Sub1
        | "mult" -> CB.add_instr self.cb I.Mult
        | "leq" -> CB.add_instr self.cb I.Leq
        | "lt" -> CB.add_instr self.cb I.Lt
        | "eq" -> CB.add_instr self.cb I.Eq
        | "curch" ->  CB.add_instr self.cb I.Curch

        | _ ->
          (* look for a primitive of that name *)
          begin match Str_map.find_opt str self.prims with
            | Some p ->
              (* load primitive *)
              let n = CB.add_local self.cb (Value.prim p) in
              CB.add_instr self.cb (I.Lload n);
              CB.add_instr self.cb I.Call;
            | None ->
              Error.failf (fun k->k"unknown instruction/prim %S" str)
          end
      end;
      recurse()

    | VM_lex.LBRACE ->
      consume self;
      (* parse sub-chunk *)
      let st' = create_st ~tok:self.tok ~env:self.env self.prims self.buf in
      begin
        parse_chunk_into_ st';
        self.tok <- st'.tok;
      end;
      rbrace self;
      (* finish sub-chunk, put it into locals *)
      let c = CB.to_chunk st'.cb in
      let n = CB.add_local self.cb (Value.chunk c) in
      CB.add_instr self.cb (I.Lload n);
      recurse()

    | VM_lex.RPAREN -> finalize();
    | VM_lex.RBRACE -> finalize();
    | VM_lex.EOI -> finalize();
  ;;

  let parse_chunk_ (self:st) : Chunk.t =
    CB.reset self.cb;
    parse_chunk_into_ self;
    CB.to_chunk self.cb

  let rec parse_stanza_ (self:st) : Stanza.t option =
    match self.tok with
    | VM_lex.EOI -> None

    | VM_lex.LPAREN ->
      consume self;
      let a = atom self in
      begin match a with
        | "def" ->
          let name = quoted_str self in
          let value = Thunk.make @@ parse_chunk_ self in
          rparen self;
          let id = Sym_ptr.str name in
          let stanza =
            Stanza.make ~id @@ Stanza.Define_meta {name; value} in
          Some stanza

        | "eval" ->
          let value = Thunk.make @@ parse_chunk_ self in
          rparen self;
          let stanza =
            let id = new_pos_id_ self in
            Stanza.make ~id @@ Stanza.Eval_meta {value} in
          Some stanza

        | "declare" ->
          let name = quoted_str self in
          let ty = Thunk.make @@ parse_chunk_ self in
          rparen self;
          let stanza =
            let id = Sym_ptr.str name in
            Stanza.make ~id @@ Stanza.Declare {name=Name.make name; ty} in
          Some stanza

        | "define" ->
          let name = quoted_str self in
          let body = Thunk.make @@ parse_chunk_ self in
          rparen self;
          let stanza =
            let id = Sym_ptr.str name in
            Stanza.make ~id @@ Stanza.Define {name=Name.make name; body} in
          Some stanza

        | "prove" ->
          (* [prove name (deps) goal proof] *)
          let name = quoted_str self in
          let p_dep self =
            lparen self;
            let name = Name.make @@ atom self in
            let kind = match quoted_str self with
              | ":eager" -> `Eager
              | ":lazy" -> `Lazy
              | s -> Error.failf (fun k->k"expected :eager or :lazy, not %S" s)
            in
            let ref = quoted_str self in
            name, kind, ref
          in
          let deps = list_of ~p:p_dep self in
          let goal = Thunk.make @@ parse_chunk_ self in

          let proof =
            (* locally bind each [dep in deps] to the proper thunk in env *)
            let local_env = Scoping_env.add_proof_deps self.env deps in
            let old_env = self.env in
            let@ () = Fun.protect ~finally:(fun() -> self.env <- old_env) in
            self.env <- local_env;
            Thunk.make @@ parse_chunk_ self
          in
          rparen self;
          let stanza =
            let id = Sym_ptr.str name in
            Stanza.make ~id @@
            Stanza.Prove {name=Name.make name; deps; goal; proof } in
          Some stanza

        | _ -> Error.failf (fun k->k"unknown stanza %S" a)
      end
    | _tok ->
      Error.failf (fun k->k"syntax error: unexpected %a" VM_lex.pp_tok _tok)

  let parse_chunk (self:t) ~env : _ result =
    let buf = Lexing.from_string ~with_positions:false self.str in
    let st = create_st self.prims buf ~env in
    begin match
        parse_chunk_into_ st;
        st.tok
      with
      | VM_lex.EOI ->
        consume st;
        let c = CB.to_chunk st.cb in
        Ok c
      | _ -> Error (Error.make "unterminated input")
      | exception Error.E err -> Error err
      | exception Failure msg -> Error (Error.make msg)
      | exception e ->
        Error (Error.of_exn e)
    end

  let parse_stanza (self:t) ~env : Scoping_env.t * (Stanza.t, _) result =
    let buf = Lexing.from_string ~with_positions:false self.str in
    let st = create_st self.prims buf ~env in
    match parse_stanza_ st with
    | exception Error.E err -> st.env, Error err
    | None -> st.env, Error (Error.make "expected stanza")
    | Some stanza ->
      let env = Scoping_env.add_stanza stanza st.env in
      env, Ok stanza

  let parse_stanzas (self:t) ~env : Scoping_env.t * (_ Vec.t, _) result =
    let buf = Lexing.from_string ~with_positions:false self.str in
    let st = create_st self.prims buf ~env in
    let vec = Vec.create() in
    let rec loop () =
      match parse_stanza_ st with
      | None -> st.env, Ok vec
      | Some stanza ->
        Vec.push vec stanza;
        st.env <- Scoping_env.add_stanza stanza st.env;
        loop ()
      | exception Error.E err ->
        st.env, Error err
    in
    loop ()

  type st_item = BRACE | PAR | BRACKET

  let needs_more (str:string) : bool =
    let st: st_item Stack.t = Stack.create() in

    let buf = Lexing.from_string ~with_positions:false str in
    let rec loop () =
      let check_pop x =
        not (Stack.is_empty st) && Stack.pop st = x
      in
      match VM_lex.token buf with
      | VM_lex.EOI -> not (Stack.is_empty st) (* unclosed { *)
      | VM_lex.LPAREN -> Stack.push PAR st; loop()
      | VM_lex.RPAREN -> check_pop PAR && loop()
      | VM_lex.LBRACKET -> Stack.push BRACKET st; loop()
      | VM_lex.RBRACKET -> check_pop BRACKET && loop()
      | VM_lex.LBRACE -> Stack.push BRACE st; loop()
      | VM_lex.RBRACE -> check_pop BRACE && loop()
      | _ -> loop()
    in
    loop()
end

(* TODO: expose instructions so that ITP can use its own syntax for VM? *)

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
  VM_.enter_chunk self c;
  VM_.run self

let eval_thunk ?debug_hook (ctx:K.Ctx.t) (th:Thunk.t) : (Value.t list, Error.t) result =
  let open Types_ in

  let open struct
    type eval_task =
      | Eval_thunk of thunk
      | Eval_chunk of thunk * chunk * vm
  end in

  let vms = Vec.create() in (* can be reused *)

  let[@inline] recycle_vm_ vm =
    VM_.reset vm;
    Vec.push vms vm;
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

  let stack: eval_task Vec.t = Vec.create() in

  Vec.push stack (Eval_thunk th);

  let eval_chunk ~th ~vm ~c : unit =
    match
      VM_.enter_chunk vm c;
      VM_.run vm;
      VM_.pop_vals vm
    with
    | vs ->
      recycle_vm_ vm;
      th.th_st <- Th_ok vs

    | exception Error.E err ->
      recycle_vm_ vm;
      th.th_st <- Th_err err;

    | exception Suspend_and_eval_chunk (th',c') ->
      (* park [c] *)
      Vec.push stack (Eval_chunk (th, c, vm));
      (* eval [c'] first *)
      Vec.push stack (Eval_chunk (th', c', alloc_vm()));

    | exception Suspend_and_resume (th', c', vm') ->
      (* park [c] *)
      Vec.push stack (Eval_chunk (th, c, vm));
      (* resume evaluation of [c'] first in [vm'] *)
      Vec.push stack (Eval_chunk (th', c', vm'));
  in

  while not (Vec.is_empty stack) do
    let task = Vec.pop_exn stack in
    match task with
    | Eval_chunk (th,c,vm) ->
      eval_chunk ~th ~vm ~c
    | Eval_thunk th ->
      begin match Thunk.state th with
        | Th_ok _ | Th_err _ -> ()
        | Th_lazy c ->
          let vm = alloc_vm() in
          eval_chunk ~th ~c ~vm
        | Th_suspended {c; vm} ->
          eval_chunk ~th ~c ~vm
      end
  done;
  Thunk.get_result_exn th

let eval_thunk1 ?debug_hook ctx th : _ result =
  match eval_thunk ?debug_hook ctx th with
  | Ok [v] -> Ok v
  | Ok vs ->
    Error (Error.makef "eval_thunk1: expected one result, got %d" (List.length vs))
  | Error _ as e -> e

let eval_stanza ?debug_hook (ctx:K.Ctx.t) (stanza:Stanza.t) : unit =
  let unwrap_ = function
    | Ok v -> v
    | Error err -> Error.raise err
  and pp_res out = function
    | Ok vs ->
      List.iter (Fmt.fprintf out "@;%a" Value.pp) vs;
    | Error err -> Fmt.fprintf out "error: %a" Error.pp err
  and pp_res1 out = function
    | Ok v -> Fmt.fprintf out "result: %a" Value.pp v
    | Error err -> Fmt.fprintf out "error: %a" Error.pp err
  in
  begin match Stanza.view stanza with
    | Stanza.Declare {name;ty} ->
      (* TODO: turn into term *)
      let ty = eval_thunk1 ?debug_hook ctx ty |> unwrap_ in
      Fmt.printf "(@[declare %a :@ %a@])@." Name.pp name Value.pp ty
    | Stanza.Define {name;body} ->
      (* TODO: turn into term *)
      let body = eval_thunk1 ?debug_hook ctx body |> unwrap_ in
      Fmt.printf "(@[define %a :=@ %a@])@." Name.pp name Value.pp body
    | Stanza.Prove {name; goal; proof} ->
      let goal = eval_thunk1 ?debug_hook ctx goal |> unwrap_ in
      let proof = eval_thunk1 ?debug_hook ctx proof in
      Fmt.printf "(@[proof %a@ :goal %a@ :proof %a@])@."
        Name.pp name Value.pp goal pp_res1 proof
    | Stanza.Define_meta {name; value} ->
      let r = eval_thunk1 ?debug_hook ctx value in
      Fmt.printf "(@[def %s =@ %a@])@." name pp_res1 r;
    | Stanza.Eval_meta {value} ->
      let r = eval_thunk ?debug_hook ctx value in
      Fmt.printf "(@[<v2>eval: %a@])@." pp_res r;
  end

let parse_chunk_string ?prims env s : _ result =
  let p = Parser.create ?prims s in
  Parser.parse_chunk ~env p

let parse_chunk_string_exn ?prims env s : Chunk.t =
  match parse_chunk_string ?prims env s with
  | Ok c -> c
  | Error e -> Error.raise e

let parse_stanza_string ?prims env s : _ * _ result =
  let p = Parser.create ?prims s in
  Parser.parse_stanza ~env p

let parse_stanza_string_exn ?prims env s : _ * Stanza.t =
  match parse_stanza_string ?prims env s with
  | env, Ok c -> env, c
  | _env, Error e -> Error.raise e


(*$inject
  let ctx = K.Ctx.create()
  let vm = create ~ctx ()
*)

(*$R
  let c = parse_chunk_string_exn Scoping_env.empty "42 2 add" in
  reset vm;
  run vm c;
  let v = pop_exn vm in
  assert_equal ~cmp:Value.equal ~printer:Value.show (Value.int 44) v
*)
