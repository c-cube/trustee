
open Sigs
open VM

type chunk = VM.Chunk.t
type stanza = VM.Stanza.t

module Scoping_env = struct
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
      add name (E_th th) self
    | Some _ -> Error.failf (fun k->k"expected %S to be a prove step" ref)
    | None -> Error.failf (fun k->k"cannot find prove step %S in env" ref)

  let add_proof_deps self l = List.fold_left add_proof_dep self l

  let add_stanza (stanza:Stanza.t) (self:t) : t =
    match Stanza.view stanza with
    | Stanza.Define_meta {name;value} ->
      add name (E_th value) self
    | Stanza.Eval_meta _ -> self
    | Stanza.Define {name; body} ->
      add name (E_define {body}) self
    | Stanza.Prove {name; deps=_; goal; proof} ->
      add name (E_prove {goal;proof}) self
    | Stanza.Declare {name; ty} ->
      add name (E_declare {ty}) self
end

type primitive_map = VM.Primitive.t Str_map.t

module Parser = struct
  module CB = Chunk_builder

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
        | "acreate" -> CB.add_instr self.cb I.Acreate
        | "apush" -> CB.add_instr self.cb I.Apush
        | "aget" -> CB.add_instr self.cb I.Aget
        | "aset" -> CB.add_instr self.cb I.Aset
        | "alen" -> CB.add_instr self.cb I.Alen
        | "aclear" -> CB.add_instr self.cb I.Aclear
        | "suem" -> CB.add_instr self.cb I.Suem;
        | "subinde" -> CB.add_instr self.cb I.Subinde;
        | "subindty" -> CB.add_instr self.cb I.Subindty;
        | "type" -> CB.add_instr self.cb I.Type
        | "var" -> CB.add_instr self.cb I.Var
        | "vty" -> CB.add_instr self.cb I.Vty
        | "tyarr" -> CB.add_instr self.cb I.Tyarr
        | "evar" -> CB.add_instr self.cb I.Evar
        | "eapp" -> CB.add_instr self.cb I.Eapp
        | "elam" -> CB.add_instr self.cb I.Elam
        | "econst" -> CB.add_instr self.cb I.Econst
        | "econst0" -> CB.add_instr self.cb I.Econst0
        | "econst1" -> CB.add_instr self.cb I.Econst1
        | "deapp" -> CB.add_instr self.cb I.Deapp
        | "delam" -> CB.add_instr self.cb I.Delam
        | "devar" -> CB.add_instr self.cb I.Devar
        | "deconst" -> CB.add_instr self.cb I.Deconst
        | "thabs" -> CB.add_instr self.cb I.Thabs
        | "thcongr" -> CB.add_instr self.cb I.Thcongr
        | "thass" -> CB.add_instr self.cb I.Thass
        | "thcut" -> CB.add_instr self.cb I.Thcut
        | "threfl" -> CB.add_instr self.cb I.Threfl
        | "thsym" -> CB.add_instr self.cb I.Thsym
        | "thtrans" -> CB.add_instr self.cb I.Thtrans
        | "thbeq" -> CB.add_instr self.cb I.Thbeq
        | "thbeqi" -> CB.add_instr self.cb I.Thbeqi
        | "thbeta" -> CB.add_instr self.cb I.Thbeta
        | "thsubst" -> CB.add_instr self.cb I.Thsubst
        | "dth" -> CB.add_instr self.cb I.Dth
        | "stopexec" -> CB.add_instr self.cb I.Stopexec
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
            Stanza.make ~id @@ Stanza.Declare {name; ty} in
          Some stanza

        | "define" ->
          let name = quoted_str self in
          let body = Thunk.make @@ parse_chunk_ self in
          rparen self;
          let stanza =
            let id = Sym_ptr.str name in
            Stanza.make ~id @@ Stanza.Define {name; body} in
          Some stanza

        | "prove" ->
          (* [prove name (deps) goal proof] *)
          let name = quoted_str self in
          let p_dep self =
            lparen self;
            let name = atom self in
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
            Stanza.Prove {name; deps; goal; proof } in
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

include Parser

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
