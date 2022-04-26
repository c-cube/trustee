
open Common_

module VM = Trustee_core.VM
module Sym_ptr = Trustee_core.Sym_ptr
module A = Ast

type stanza = VM.Stanza.t
type thunk = VM.Thunk.t

module Env = struct
  module M = Str_map

  type t = {
    ths: thunk M.t;
  }

  let empty : t = {ths=M.empty}

  let find name (self:t) : thunk option =
    M.find_opt name self.ths

  let add name th (self:t) : t =
    {ths=M.add name th self.ths}

  let add_stanza self (st:VM.Stanza.t) : t =
    match VM.Stanza.view st with
    | VM.Stanza.Define_meta {name; value} ->
      add name value self
    | VM.Stanza.Eval_meta _ -> self
    | VM.Stanza.Declare _
    | VM.Stanza.Define _
    | VM.Stanza.Prove _
      -> self (* TODO *)
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

  type local = {
    lreg: int;
    lvar: bool;
  }

  type st = {
    mutable locals: local Str_map.t;
    cb: CB.t;
    env: Env.t;
    fun_name: string option;
    mutable n_regs: int; (* current number of registers, evolves over time *)
    mutable free_regs: int list;
  }

  let create ?fun_name env ~n : st =
    { locals=Str_map.empty; env; fun_name;
      cb=CB.create ~n_args:n ~n_ret:1 (); n_regs=n;
      free_regs=[] }

  let alloc_reg self =
    match self.free_regs with
    | x :: tl ->
      self.free_regs <- tl;
      x
    | [] ->
      let n = self.n_regs in
      self.n_regs <- 1 + self.n_regs;
      n

  let recycle_reg self n =
    self.free_regs <- n :: self.free_regs

  let with_new_var self f =
    let reg = alloc_reg self in
    Fun.protect (fun () -> f reg) ~finally:(fun() -> recycle_reg self reg)

  let rec compile_expr (self:st) (e:A.expr) : unit =
    let recurse e = compile_expr self e in

    let loc = e.loc in
    match With_loc.view e with
    | A.E_app (f, args) ->
      let n = List.length args in
      let args = List.rev args in
      List.iter recurse args;
      compile_var self f;
      CB.push_i self.cb (I.call n);

    | A.E_var s ->
      compile_var self s

    | A.E_array_lit l ->
      begin
        let@ reg = with_new_var self in
        CB.push_i self.cb I.acreate;
        (* store copy into <reg> *)
        CB.push_i self.cb I.dup;
        CB.push_i self.cb (I.rstore reg);
        (* for each [x in l], with the array
           [dup; <compile x>; apush] *)
        List.iter
          (fun x ->
             CB.push_i self.cb I.dup;
             recurse x;
             CB.push_i self.cb I.apush)
          l;
      end

    | A.E_binop (op, a, b) ->
      let default_args()=
        recurse a;
        recurse b;
      in
      begin match op with
        | A.Plus ->
          default_args(); CB.push_i self.cb I.add
        | A.Minus ->
          default_args(); CB.push_i self.cb I.sub
        | A.Times ->
          default_args(); CB.push_i self.cb I.mult
        | A.Div -> Error.failf ~loc (fun k->k"TODO: div")
        | A.Eq ->
          default_args(); CB.push_i self.cb I.eq;
        | A.Neq ->
          default_args();
          CB.push_i self.cb I.eq;
          CB.push_i self.cb I.not
        | A.And -> Error.failf ~loc (fun k->k"TODO: and")
        | A.Or -> Error.failf ~loc (fun k->k"TODO: or")
        | A.Leq ->
          default_args(); CB.push_i self.cb I.leq
        | A.Lt ->
          default_args(); CB.push_i self.cb I.lt
        | A.Geq ->
          recurse b; recurse a; CB.push_i self.cb I.leq
        | A.Gt ->
          recurse b; recurse a; CB.push_i self.cb I.lt
      end

    | A.E_unop (op, a) ->
      begin match op with
        | A.Not ->
          recurse a;
          CB.push_i self.cb I.not

        | A.Uminus ->
          CB.push_i self.cb (I.int 0);
          recurse a;
          CB.push_i self.cb I.sub (* 0 - a *)
      end;

    | A.E_if {test; then_; elseif; else_} ->

      let branch_ends = ref [] in

      let compile_branch (test, then_) =
        (* test expr, then test *)
        compile_expr self test;
        let last_pos = CB.cur_pos self.cb in
        CB.push_i self.cb I.nop;
        CB.push_comment self.cb "if";

        (* test is true: execute block *)
        compile_block_return self then_;

        (* jump over the other branches *)
        let success_pos = CB.cur_pos self.cb in
        branch_ends := success_pos :: !branch_ends;
        CB.push_i self.cb I.nop;

        (* now that block is done, insert a jump over it
           if test is false *)
        CB.set_i self.cb last_pos (I.jifn @@ CB.cur_pos self.cb);
      in

      compile_branch (test,then_);
      List.iter compile_branch elseif;

      begin match else_ with
        | None -> CB.push_i self.cb I.nil
        | Some bl ->
          compile_block_return self bl;
      end;

      (* jump here from successful branches *)
      let here = CB.cur_pos self.cb in
      List.iter (fun pos ->
          CB.set_i self.cb pos (I.jmp here))
        !branch_ends;

    | A.E_block bl ->
      let ret = compile_block self bl in
      if not ret then CB.push_i self.cb I.nil

    | A.E_const c ->
      begin match c with
        | A.C_unit -> CB.push_i self.cb I.nil
        | A.C_int i -> CB.push_i self.cb (I.int i)
        | A.C_string s ->
          let local = CB.add_local self.cb (VM.Value.string s) in
          CB.push_i self.cb (I.lload local)
        | A.C_bool b -> CB.push_i self.cb (I.bool b)

        | A.C_atom _ ->
          Error.failf ~loc (fun k->k"TODO: atoms")
      end

    | A.E_logic _ ->
      assert false

  (* compile a constant or variable *)
  and compile_var (self:st) (s:A.var) : unit =
    match Str_map.find_opt s.view self.locals with
    | Some {lreg;_} ->
      CB.push_comment self.cb (spf "deref %s" s.view);
      CB.push_i self.cb (I.rload lreg);
    | None ->
      match Env.find s.view self.env, self.fun_name with
      | Some th, _ ->
        let local = CB.add_local self.cb (VM.Value.thunk th) in
        CB.push_i self.cb (I.lload local);
        CB.push_i self.cb I.tforce;
      | None, Some name when s.view = name ->
        (* recursive call *)
        CB.push_i self.cb I.curch;
      | None, _ ->
        Error.failf ~loc:s.loc
          (fun k->k"Variable %S is not in scope" s.view)

  and compile_block (self:st) (bl:A.block) : bool =
    compile_block_items self bl.view.bl_items

  and compile_block_return self bl : unit =
    let ret = compile_block self bl in
    if not ret then CB.push_i self.cb I.nil;
    ()

  and compile_block_noreturn self bl : unit =
    let ret = compile_block self bl in
    if ret then CB.push_i self.cb I.drop;
    ()

  (* compile block; return [true] iff a value is on the stack *)
  and compile_block_items (self:st) (l:A.block_item list) : bool =
    let old_locals = self.locals in
    let local_regs = ref [] in

    let returns = ref false in
    let clear_stack () =
      if !returns then CB.push_i self.cb I.drop
    in

    let rec loop l =
      match l with
      | [] -> ()

      | [{With_loc.view=A.Bl_eval e; _}] ->
        clear_stack();
        compile_expr self e;
        returns := true;

      | {With_loc.view=A.Bl_eval e; _} :: tl ->
        clear_stack();
        compile_expr self e;
        returns := true;

        loop tl

      | {With_loc.view=A.Bl_let (v, e); _} :: tl ->
        clear_stack();

        (* allocate local var for [v] *)
        let reg = alloc_reg self in
        local_regs := reg :: !local_regs;
        compile_expr self e;
        CB.push_comment self.cb v.view;
        CB.push_i self.cb (I.rstore reg);
        self.locals <- Str_map.add v.view {lreg=reg; lvar=false} self.locals;

        loop tl

      | {With_loc.view=A.Bl_var (v, e); _} :: tl ->
        clear_stack();

        (* allocate local var for [v] *)
        let reg = alloc_reg self in
        local_regs := reg :: !local_regs;
        compile_expr self e;
        CB.push_comment self.cb (spf "var %s" v.view);
        CB.push_i self.cb (I.rstore reg);
        self.locals <- Str_map.add v.view {lreg=reg; lvar=true} self.locals;

        loop tl

      | {With_loc.view=A.Bl_assign (v, e); loc} :: tl ->

        clear_stack();
        begin match Str_map.find_opt v.view self.locals with
          | Some {lreg; lvar=true} ->
            compile_expr self e;
            CB.push_i self.cb (I.rstore lreg);

          | Some _ ->
            Error.failf ~loc (fun k->k"cannot assign %S, it is not a variable" v.view)

          | None ->
            Error.failf ~loc (fun k->k"cannot assign unknown variable %S" v.view)
        end;

        loop tl

      | {With_loc.view=A.Bl_block bl; _} :: tl ->
        clear_stack();

        returns := compile_block self bl;
        loop tl

      | {With_loc.view=A.Bl_while (cond,bl); loc} :: tl ->

        clear_stack();

        let pos_start = CB.cur_pos self.cb in
        compile_expr self cond;
        let pos_test = CB.cur_pos self.cb in
        CB.push_comment self.cb "exit while";
        CB.push_i self.cb I.nop; (* placeholder *)
        compile_block_noreturn self bl;
        CB.push_i self.cb (I.jmp pos_start); (* back to start *)

        (* at [pos_test], insert a jump here if test is false *)
        let pos_end = CB.cur_pos self.cb in
        CB.set_i self.cb pos_test (I.jifn pos_end);

        loop tl

      | {With_loc.view=A.Bl_continue; loc} :: _ ->
        Error.failf ~loc (fun k->k"TODO: continue")

      | {With_loc.view=A.Bl_break; loc} ::  _ ->
        Error.failf ~loc (fun k->k"TODO: break")

      | {With_loc.view=A.Bl_return _; loc} ::  _ ->
        Error.failf ~loc (fun k->k"TODO: return")

    in
    loop l;
    self.locals <- old_locals;
    List.iter (recycle_reg self) !local_regs;
    !returns

  let compile_fn ~env ?fun_name vars body : VM.Chunk.t =
    let st = create env ?fun_name ~n:(List.length vars) in
    let vars = List.rev vars in
    (* registers are assigned to [vars] already, just reflect that
       in the [locals] *)
    List.iteri
      (fun i (v:A.var) ->
         st.locals <- Str_map.add v.view {lreg=i; lvar=false} st.locals)
      vars;
    let ret = compile_block st body in
    if not ret then CB.push_i st.cb I.nil; (* make sure we return sth *)
    (* TODO: be able to return multiple values? *)
    CB.push_i st.cb I.ret;
    CB.to_chunk st.cb

  let gen_sym_pos_ =
    let n = ref 0 in
    fun() -> incr n; !n

  let top (env:Env.t) (p:A.statement) : Env.t * _ list =
    let stanzas =
      match With_loc.view p with
      | A.S_fn (f,vars,bl) ->
        let id = Sym_ptr.(namespace "fn" @@ str f.view) in
        let st = create env ~n:0 in

        (* chunk that just returns the function *)
        let c_fn = compile_fn ~fun_name:f.view ~env vars bl in
        let local = CB.add_local st.cb (VM.Value.chunk c_fn) in
        CB.push_i st.cb (I.lload local);
        CB.push_i st.cb I.ret;
        let c = CB.to_chunk st.cb in

        let value = VM.Thunk.make c in
        [ VM.Stanza.(make ~id @@ Define_meta {name=f.view; value}) ]

      | A.S_eval e ->
        let id = Sym_ptr.(namespace "eval" @@ pos (gen_sym_pos_())) in
        let st = create env ~n:0 in
        compile_expr st e;
        CB.push_i st.cb I.ret;
        let c = CB.to_chunk st.cb in
        let value = VM.Thunk.make c in
        [ VM.Stanza.(make ~id @@ Eval_meta {value}) ]
    in
    let env = List.fold_left Env.add_stanza env stanzas in
    env, stanzas
end

let compile = Compile_.top

let compile_l = CCList.fold_flat_map compile
