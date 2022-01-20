
module T = Trustee_core

module ITP = Trustee_itp

module Log = T.Log
module K = T.Kernel
module Loc = T.Loc
module PA = Trustee_syntax.Parse_ast
module TA = Trustee_syntax.Type_ast
module Syntax = Trustee_syntax.Syntax

module Linol = Linol.Make(Linol.Blocking_IO)
module Position = Linol.Position
module Range = Linol.Range
module LP = Lsp.Types

let lsp_pos_of_pos (p:T.Position.t) : Position.t =
  Position.create ~line:(p.line-1) ~character:(p.col-1)

let pos_of_lsp_pos (p:Position.t) : T.Position.t =
  T.Position.make ~line:(p.line+1) ~col:(p.character+1)

let lsp_range_of_loc (l:T.Loc.t) : Range.t =
  Range.create ~start:(lsp_pos_of_pos l.start) ~end_:(lsp_pos_of_pos l.end_)

type parsed_buffer = {
  penv: PA.Env.t;
  env: TA.Ty_env.t;
  idx: TA.Index.t;
}

let ident_under_pos ~file (s:string) (pos:T.Position.t) : (string * Loc.t) option =
  let open Syntax in
  let module Str = Trustee_syntax.Tok_stream in
  let toks = Lexer.create ~file s in
  let rec find () =
    if Str.is_done toks then None
    else (
      match Str.cur toks with
      | SYM s, loc when Loc.contains loc pos -> Some (s, loc)
      | _, loc when T.Position.leq pos loc.start -> None (* gone far enough *)
      | _ ->
        Str.junk toks;
        find()
    )
  in
  find()

let trustee_server _ctx = object (self)
    inherit Linol.server

    (* one env per document *)
    val buffers: (LP.DocumentUri.t, parsed_buffer) Hashtbl.t = Hashtbl.create 32

    method private _on_doc
        ~(notify_back:Linol.notify_back) (d:LP.DocumentUri.t) (content:string) =
      (* TODO: use penv/env from dependencies, if any, once we have import *)

      let penv = PA.Env.create () in
      let stmts =
        Syntax.parse_top_l_process
          ~file:d ~env:penv
          (Syntax.Lexer.create ~file:d content)
      in
      Log.debugf 3 (fun k->k "for %s: parsed %d statements" d (List.length stmts));

      let diags = ref [] in
      let tyst = TA.Typing_state.create _ctx in
      let idx = List.fold_left
          (fun idx stmt ->
             TA.process_stmt idx tyst
               ~on_show:(fun loc msg ->
                   let range = lsp_range_of_loc loc in
                   let message = Fmt.asprintf "@[%a@]" msg() in
                   Log.debugf 5 (fun k->k"LSP info loc: %a"
                                    Yojson.Safe.pp (Range.yojson_of_t range));
                   let d = LP.Diagnostic.create
                       ~severity:LP.DiagnosticSeverity.Information
                       ~range ~message () in
                   diags := d :: !diags
                 )
               ~on_error:(fun loc e ->
                   let range = lsp_range_of_loc loc in
                   let message = Fmt.asprintf "@[%a@]" e() in
                   let d = LP.Diagnostic.create
                       ~severity:LP.DiagnosticSeverity.Error ~range ~message () in
                   diags := d :: !diags
                 )
               stmt)
          TA.Index.empty stmts
      in

      let env = TA.Typing_state.ty_env tyst in
      Hashtbl.replace buffers d {penv; env; idx};

      let diags = List.rev !diags in
      Log.debugf 2 (fun k->k"send back %d diagnostics" (List.length diags));
      notify_back#send_diagnostic diags

    method on_notif_doc_did_open ~notify_back d ~content : unit =
      Log.debugf 2 (fun k->k "did open %s (%d bytes)" d.uri (String.length content));
      self#_on_doc ~notify_back d.uri content

    method on_notif_doc_did_close ~notify_back:_ d : unit =
      Log.debugf 2 (fun k->k "did close %s" d.uri);
      Hashtbl.remove buffers d.uri;
      ()

    method on_notif_doc_did_change ~notify_back d _c ~old_content:_old ~new_content : unit =
      Log.debugf 5 (fun k->k "did update %s (%d bytes -> %d bytes)" d.uri
                   (String.length _old) (String.length new_content));
      self#_on_doc ~notify_back d.uri new_content

    (* ## requests ## *)

    method! on_req_hover ~notify_back:_ ~id:_ ~uri ~pos (_d:Linol.doc_state) : _ option =
      match Hashtbl.find buffers uri with
      | exception Not_found -> None
      | {idx; _} ->
        let pos = pos_of_lsp_pos pos in
        Log.debugf 1
          (fun k->k"lookup in idx (size %d) at pos %a"
              (TA.Index.size idx) T.Position.pp pos);
        let r =
          match TA.Index.find idx pos with
          | [] -> None
          | q :: _ ->
            Log.debugf 5 (fun k->k"found %a" q#pp ());
            let s = Fmt.to_string q#pp () in
            let r = LP.Hover.create
                ~contents:(`MarkedString {LP.MarkedString.value=s; language=None})
                ~range:(lsp_range_of_loc q#loc) ()
            in
            Some r
        in
        r

    method! on_req_definition ~notify_back:_ ~id:_ ~uri ~pos _st : _ option =
      match Hashtbl.find buffers uri with
      | exception Not_found -> None
      | {idx;_} ->
        let pos = pos_of_lsp_pos pos in
        Log.debugf 1
          (fun k->k"lookup for def in idx (size %d) at pos %a"
              (TA.Index.size idx) T.Position.pp pos);
        let r =
          match TA.Index.find idx pos with
          | [] -> None
          | q :: _ ->
            match q#def_loc with
            | None -> None
            | Some loc ->
              Log.debugf 5 (fun k->k"found def at %a" T.Loc.pp q#loc);
              let loc =
                LP.Location.create ~uri:loc.T.Loc.file ~range:(lsp_range_of_loc loc) in
              let r = `Location [loc] in
              (* Log.debugf 20 (fun k->k"response: %a" Yojson.Safe.pp (Locations.yojson_of_t r)); *)
              Some r
        in
        r

    method! on_req_completion ~notify_back:_ ~id:_ ~uri ~pos ~ctx:_ doc_st : _ option =
      match Hashtbl.find buffers uri with
      | exception Not_found -> None
      | {idx;_} ->
        let pos = pos_of_lsp_pos pos in
        Log.debugf 5 (fun k->k"completion at %a" T.Position.pp pos);
        (* find token under the cursor, if any *)
        begin match ident_under_pos ~file:uri doc_st.content pos with
          | None -> None
          | Some (ident, ident_loc) ->
            Log.debugf 5 (fun k->k"req-completion: ident `%s`" ident);

            let tyenv = TA.Index.find_ty_env idx pos in
            Log.debugf 10 (fun k->k"req-completion: env@ %a" TA.Ty_env.pp tyenv);

            let compls =
              TA.Ty_env.completions tyenv ident
            in
            Log.debugf 5
              (fun k->k"completions: %a" (Fmt.Dump.list Fmt.string)
                  (Iter.map fst compls |> Iter.to_list));
            let compls =
              compls
              |> Iter.take 20
              |> Iter.map
                (fun (name, c) ->
                  let lbl, kind = match c with
                    | TA.Ty_env.N_const _ -> "C", LP.CompletionItemKind.Value
                    | TA.Ty_env.N_thm _ -> "T", LP.CompletionItemKind.Value
                    | TA.Ty_env.N_rule  _ -> "R", LP.CompletionItemKind.Operator
                  in
                  let label = Printf.sprintf "%s %s" lbl name in
                  let textEdit =
                    LP.TextEdit.create ~range:(lsp_range_of_loc ident_loc)
                      ~newText:name
                  in
                  let ci = LP.CompletionItem.create
                    ~label ~kind ~textEdit
                    ~detail:(TA.Ty_env.string_of_named_object c)
                    ()
                  in
                  Log.debugf 50
                    (fun k->k"compl item: %a"
                        Yojson.Safe.pp (LP.CompletionItem.yojson_of_t ci));
                  ci
                )
              |> Iter.to_list
            in
            Log.debugf 5 (fun k->k"send back %d completions" (List.length compls));
            Some (`List compls)
        end
  end

let setup_logger_ () =
  ITP.Logger.setup_trustee();
  let reporter = ITP.Logger.create() in
  Logs.set_reporter (ITP.Logger.as_reporter reporter);

  let dbg = Sys.getenv_opt "LSPLOG"=Some"1" in
  Logs.set_level ~all:true (Some (if dbg then Logs.Debug else Logs.Info));

  if true || dbg  then (
    let oc = open_out "/tmp/lsp.log" in
    ITP.Logger.log_to_chan reporter oc;
    at_exit (fun () -> flush oc; close_out_noerr oc);
    Log.set_level 50;
  )

let () =
  setup_logger_ ();
  let ctx = K.Ctx.create() in
  let server = trustee_server ctx in
  let task = Linol.create_stdio server in
  match Linol.run task with
  | exception e ->
    let e = Printexc.to_string e in
    Log.debugf 1 (fun k->k"error: %s" e);
    Printf.eprintf "error: %s\n%!" e;
    exit 1
  | () -> ()