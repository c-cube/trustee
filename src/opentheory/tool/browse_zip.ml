(** Browse an opentheory proof zip via the hx_inspect recursive interface.

    Usage: trustee_browse_zip --zip <file.zip> [-p <port>]

    Starts a tiny_httpd server on 127.0.0.1:<port> (default 8085) serving the
    entire archive at [/hx_inspect/]. Every theory, theorem, proof step, and
    expression is recursively expandable. *)

open Trustee_opentheory
open Common_
open Hx_inspect

open struct
  let spf = Printf.sprintf
  let truncate ~max_len s =
    if String.length s > max_len then
      String.sub s 0 max_len ^ "…"
    else
      s
end

(* ── tiny HTML construction helpers ───────────────────────────── *)

module H = struct
  let div ?cls () cs =
    Html.div
      (Option.map (fun c -> [ "class", c ]) cls |> Option.value ~default:[])
      cs

  let span ?cls () cs =
    Html.span
      (Option.map (fun c -> [ "class", c ]) cls |> Option.value ~default:[])
      cs

  let ul ?cls () cs =
    Html.ul
      (Option.map (fun c -> [ "class", c ]) cls |> Option.value ~default:[])
      cs

  let li ?cls () cs =
    Html.li
      (Option.map (fun c -> [ "class", c ]) cls |> Option.value ~default:[])
      cs

  let p ?cls () cs =
    Html.p
      (Option.map (fun c -> [ "class", c ]) cls |> Option.value ~default:[])
      cs

  let h3 s = Html.h3 [] [ Node.txt s ]
  let h4 s = Html.h4 [] [ Node.txt s ]
  let h2 s = Html.h2 [] [ Node.txt s ]
  let strong s = Html.strong [] [ Node.txt s ]
  let txtf fmt = Printf.ksprintf (fun s -> Node.txt s) fmt
  let br = Html.br []
  let hr = Html.hr []
  let sub ~key ~ops v = Node.sub ~key ~ops:(lazy ops) v
end

(* ── widget helpers ────────────────────────────────────────────── *)

let indexed_subs ~key_prefix ~ops l =
  let ops = lazy ops in
  List.mapi (fun i x -> Node.sub ~key:(spf "%s-%d" key_prefix i) ~ops x) l

let kv ~key ?(attrs = []) v =
  H.span ~cls:"kv" ()
    [
      H.span ~cls:"kv-key" () [ Node.txt (key ^ " ") ];
      Html.span attrs [ v ];
    ]

let opt_section ~attrs ~title ~key_prefix ~ops l =
  if l = [] then
    Node.txt ""
  else
    Html.div attrs
      ([ H.h4 title ] @ indexed_subs ~key_prefix ~ops l)

(* ── root state ───────────────────────────────────────────────── *)
type root_st = {
  zh: Proof_zip.zip_handle;
  ctx: K.Ctx.t;
  names: string list;
}

(* ── expression ops (recursive lazy) ──────────────────────────── *)

let rec expr_ops_lazy : K.Expr.t Node.ops Lazy.t =
  lazy (Node.Ops.make ~view:expr_view ~summary:expr_summary ())

and expr_summary (e : K.Expr.t) : string =
  truncate ~max_len:80 (Fmt.asprintf "%a" K.Expr.pp e)

and expr_view (e : K.Expr.t) : Node.t =
  let ops = Lazy.force expr_ops_lazy in
  let sub_e ~key = H.sub ~key ~ops in
  match K.Expr.view e with
  | K.E_kind -> Node.txt "kind"
  | K.E_type -> Node.txt "type"
  | K.E_var v ->
    H.span ~cls:"expr expr-var" ()
      [ H.txtf "%s : " (K.Var.name v); sub_e ~key:"ty" (K.Var.ty v) ]
  | K.E_bound_var v ->
    H.span ~cls:"expr expr-bvar" ()
      [ H.txtf "db_%d : " v.bv_idx; sub_e ~key:"ty" v.bv_ty ]
  | K.E_const (c, []) ->
    H.span ~cls:"expr expr-const" ()
      [ H.txtf "%s : " (K.Const.name c); sub_e ~key:"ty" (K.Expr.ty_exn e) ]
  | K.E_const (c, args) ->
    let name = K.Const.name c in
    H.div ~cls:"expr expr-const-app" ()
      ([ H.strong (spf "%s" name) ]
      @ (if args <> [] then
           H.span () [ Node.txt " args:" ]
           :: List.mapi (fun i a -> H.sub ~key:(spf "arg-%d" i) ~ops a) args
         else
           [])
      @ [ H.span () [ Node.txt " : " ]; sub_e ~key:"ty" (K.Expr.ty_exn e) ])
  | K.E_app (f, a) ->
    H.div ~cls:"expr expr-app" ()
      [
        H.span () [ Node.txt "app(" ];
        sub_e ~key:"f" f;
        H.span () [ Node.txt " " ];
        sub_e ~key:"arg" a;
        H.span () [ Node.txt ")" ];
      ]
  | K.E_lam (n, ty, bod) ->
    H.div ~cls:"expr expr-lam" ()
      [
        H.txtf "λ%s:" n;
        sub_e ~key:"ty" ty;
        H.span () [ Node.txt ". " ];
        sub_e ~key:"body" bod;
      ]
  | K.E_arrow (a, b) ->
    H.div ~cls:"expr expr-arrow" ()
      [ sub_e ~key:"dom" a; H.span () [ Node.txt " → " ]; sub_e ~key:"codom" b ]
  | K.E_box seq ->
    H.div ~cls:"expr expr-box" ()
      [
        H.span () [ Node.txt "□(" ];
        sub_e ~key:"seq" (K.Sequent.concl seq);
        H.span () [ Node.txt ")" ];
      ]

(* ── sequent ops ──────────────────────────────────────────────── *)

let sequent_ops : K.sequent Node.ops =
  Node.Ops.make
    ~view:(fun seq ->
      let ops = Lazy.force expr_ops_lazy in
      let hyps = K.Sequent.hyps_l seq in
      let concl = K.Sequent.concl seq in
      H.div ~cls:"sequent" ()
        (indexed_subs ~key_prefix:"hyp" ~ops hyps
        @ [
            H.span ~cls:"vdash" () [ Node.txt " ⊢ " ];
            H.sub ~key:"concl" ~ops concl;
          ]))
    ~summary:(fun seq ->
      spf "⊢ %s"
        (truncate ~max_len:60
           (Fmt.asprintf "%a" K.Expr.pp (K.Sequent.concl seq))))
    ()

(* ── proof-step ops ───────────────────────────────────────────── *)

let proof_step_ops : (K.Linear_proof.step * int) Node.ops =
  let subst_arg su =
    H.ul ~cls:"proof-arg-subst" ()
      (List.map
         (fun (v, e) ->
           H.li ()
             [
               H.txtf "%s := " (K.Var.name v);
               H.sub ~key:(K.Var.name v) ~ops:(Lazy.force expr_ops_lazy) e;
             ])
         su)
  in
  Node.Ops.make
    ~view:(fun ((step : K.Linear_proof.step), idx) ->
      let ops = Lazy.force expr_ops_lazy in
      let arg_node = function
        | K.Proof.Pr_expr e -> H.sub ~key:"expr" ~ops e
        | K.Proof.Pr_subst su -> subst_arg su
      in
      let parents =
        match step.parents with
        | [] -> []
        | ps ->
          [
            H.span ~cls:"proof-parents" ()
              [
                Node.txt
                  (spf "[ %s ]"
                     (String.concat ", " (List.map string_of_int ps)));
              ];
          ]
      in
      H.div ~cls:"proof-step" ()
        ([ H.strong (spf "[%d] %s" idx step.rule) ]
        @ List.concat_map (fun a -> [ Node.txt " "; arg_node a ]) step.args
        @ parents
        @ [ H.br; H.sub ~key:"seq" ~ops:sequent_ops step.concl ]))
    ~summary:(fun (step, idx) ->
      spf "[%d] %s: %s" idx step.rule
        (truncate ~max_len:50
           (Fmt.asprintf "%a" K.Sequent.pp step.concl)))
    ()

(* ── linear-proof ops ─────────────────────────────────────────── *)

let linear_proof_ops : (string * int * K.Linear_proof.t) Node.ops =
  Node.Ops.make
    ~view:(fun (thy_name, thm_idx, lp) ->
      let n_steps = K.Linear_proof.steps lp |> Iter.length in
      H.div ~cls:"proof" ()
        [
          H.p ()
            [
              H.txtf "Proof for theorem %d in %s (%d steps)" thm_idx thy_name
                n_steps;
            ];
          H.div ~cls:"proof-steps" ()
            (K.Linear_proof.steps lp
            |> Iter.map (fun (i, step) ->
                   H.sub ~key:(spf "step-%d" i) ~ops:proof_step_ops (step, i))
            |> Iter.to_list);
        ])
    ~summary:(fun (_thy_name, _thm_idx, lp) ->
      let n = K.Linear_proof.steps lp |> Iter.length in
      spf "%d steps" n)
    ()

(* ── thm-data ─────────────────────────────────────────────────── *)

type thm_data = {
  thy_name: string;
  thm_idx: int;
  thm: K.Thm.t;
  zh: Proof_zip.zip_handle;
  ctx: K.Ctx.t;
}

let theorem_ops : thm_data Node.ops =
  Node.Ops.make
    ~view:(fun (td : thm_data) ->
      let ops = Lazy.force expr_ops_lazy in
      let hyps = K.Thm.hyps_l td.thm in
      let concl = K.Thm.concl td.thm in
      let has_proof =
        match Proof_zip.load_proofs td.zh ~ctx:td.ctx td.thy_name with
        | None -> false
        | Some proofs -> List.length proofs > td.thm_idx
      in
      H.div ~cls:"theorem" ()
        ([ H.h4 (spf "Theorem %d in %s" td.thm_idx td.thy_name) ]
        @ List.mapi
            (fun i h ->
              H.div ~cls:"thm-hyp" ()
                [ H.txtf "hyp %d: " i; H.sub ~key:(spf "hyp-%d" i) ~ops h ])
            hyps
        @ [
            H.div ~cls:"thm-concl" ()
              [ H.strong "⊢ "; H.sub ~key:"concl" ~ops concl ];
          ]
        @
        if has_proof then
          [
            H.hr;
            H.sub ~key:"proof" ~ops:linear_proof_ops
              ( td.thy_name,
                td.thm_idx,
                Option.get (Proof_zip.load_proofs td.zh ~ctx:td.ctx td.thy_name)
                |> fun proofs -> List.nth proofs td.thm_idx );
          ]
        else
          [ H.p ~cls:"no-proof" () [ Node.txt "(no proof data)" ] ]))
    ~summary:(fun (td : thm_data) ->
      truncate ~max_len:70
        (Fmt.asprintf "%a" (K.Thm.pp_depth ~max_depth:3) td.thm))
    ()

(* ── const-data ───────────────────────────────────────────────── *)

type const_data = {
  const: K.Const.t;
  ctx: K.Ctx.t;
}

let const_ops : const_data Node.ops =
  Node.Ops.make
    ~view:(fun (cd : const_data) ->
      let ops = Lazy.force expr_ops_lazy in
      let name = K.Const.name cd.const in
      let ty = K.Const.ty cd.const in
      let def_info =
        match K.Const.get_def cd.ctx cd.const with
        | Some def ->
          let approx = K.Const_def.approx_def def in
          [
            H.div ~cls:"const-def" ()
              [
                H.strong "Definition: ";
                Node.txt
                  (match approx with
                  | `Param -> "theory parameter"
                  | `Def rhs -> Fmt.asprintf "= %a" K.Expr.pp rhs
                  | `Ty_def phi ->
                    Fmt.asprintf "type predicate = %a" K.Expr.pp phi
                  | `Other -> "opaque");
              ];
          ]
        | None ->
          [
            H.p ~cls:"const-no-def" () [ Node.txt "(no definition available)" ];
          ]
      in
      H.div ~cls:"const" ()
        ([ H.h4 (spf "Constant %s" name) ]
        @ [
            kv ~key:"Type:"
              ~attrs:[ "class", "const-type" ]
              (H.sub ~key:"ty" ~ops ty);
            kv ~key:"Args:"
              ~attrs:[ "class", "const-args" ]
              (Node.txt
                 (Fmt.asprintf "%a" K.Const.pp_args (K.Const.args cd.const)));
          ]
        @ def_info))
    ~summary:(fun (cd : const_data) ->
      Fmt.asprintf "%s : %a" (K.Const.name cd.const) K.Expr.pp
        (K.Const.ty cd.const))
    ()

(* ── theory ops ───────────────────────────────────────────────── *)

type thy_data = {
  thy_name: string;
  zh: Proof_zip.zip_handle;
  ctx: K.Ctx.t;
}

let mk_thm_data thy_name zh ctx i thm = { thy_name; thm_idx = i; thm; zh; ctx }
let mk_const_data ctx c = { const = c; ctx }

let theory_ops : thy_data Node.ops =
  Node.Ops.make
    ~view:(fun (td : thy_data) ->
      match Proof_zip.load_theory td.zh ~ctx:td.ctx td.thy_name with
      | None ->
        H.p ~cls:"error" () [ H.txtf "Could not load theory: %s" td.thy_name ]
      | Some thy ->
        let param_consts = K.Theory.param_consts thy in
        let param_thms = K.Theory.param_theorems thy in
        let consts = K.Theory.consts thy in
        let theorems = K.Theory.theorems thy in
        H.div ~cls:"theory" ()
          [
            H.h3 (spf "Theory %s" td.thy_name);
            (if param_consts <> [] || param_thms <> [] then
               H.div ~cls:"theory-axioms" ()
                 ([ H.h4 "Axioms" ]
                 @ indexed_subs ~key_prefix:"ax-const" ~ops:const_ops
                     (List.map (mk_const_data td.ctx) param_consts)
                 @ indexed_subs ~key_prefix:"ax-thm" ~ops:theorem_ops
                     (List.mapi
                        (mk_thm_data td.thy_name td.zh td.ctx)
                        param_thms))
             else
               Node.txt "");
            opt_section
              ~attrs:[ "class", "theory-consts" ]
              ~title:"Defined constants" ~key_prefix:"const" ~ops:const_ops
              (List.map (mk_const_data td.ctx) consts);
            opt_section
              ~attrs:[ "class", "theory-theorems" ]
              ~title:"Theorems" ~key_prefix:"thm" ~ops:theorem_ops
              (List.mapi (mk_thm_data td.thy_name td.zh td.ctx) theorems);
          ])
    ~summary:(fun (td : thy_data) ->
      match Proof_zip.load_theory td.zh ~ctx:td.ctx td.thy_name with
      | None -> spf "%s (error)" td.thy_name
      | Some thy ->
        let n_axioms =
          List.length (K.Theory.param_consts thy)
          + List.length (K.Theory.param_theorems thy)
        in
        let n_consts = List.length (K.Theory.consts thy) in
        let n_thms = List.length (K.Theory.theorems thy) in
        spf "%s (%d axioms, %d consts, %d thms)" td.thy_name n_axioms n_consts
          n_thms)
    ()

(* ── root ops ─────────────────────────────────────────────────── *)

let root_ops : root_st Node.ops =
  Node.Ops.make
    ~view:(fun (st : root_st) ->
      H.div ~cls:"root" ()
        [
          H.h2 "Opentheory Archive";
          H.p () [ H.txtf "%d theories in archive" (List.length st.names) ];
          H.div ~cls:"theory-list" ()
            (List.map
               (fun name ->
                 H.sub ~key:name ~ops:theory_ops
                   { thy_name = name; zh = st.zh; ctx = st.ctx })
               st.names);
        ])
    ~summary:(fun (st : root_st) ->
      spf "Opentheory archive (%d theories)" (List.length st.names))
    ()

(* ── main ─────────────────────────────────────────────────────── *)

let () =
  let zip_file = ref "" in
  let port = ref 8085 in
  Arg.parse
    [
      "--zip", Arg.Set_string zip_file, " <file> path to proof zip file";
      "-p", Arg.Set_int port, " <n> port (default 8085)";
      "--port", Arg.Set_int port, " <n> port";
    ]
    (fun s -> raise (Arg.Bad (spf "unexpected argument: %s" s)))
    "trustee_browse_zip --zip <file.zip> [-p <port>]";
  if !zip_file = "" then (
    Printf.eprintf "error: --zip <file.zip> is required\n%!";
    exit 1
  );
  let zh = Proof_zip.open_zip !zip_file in
  let names =
    List.sort String.compare (Proof_zip.theory_names zh)
    |> List.filter (fun n -> not (CCString.prefix ~pre:"_storage/" n))
  in
  Printf.printf "opened %s: %d theories\n%!" !zip_file (List.length names);
  let ctx = K.Ctx.create ~store_proofs:false () in
  Proof_zip.restore_storage zh ctx;
  Printf.printf "restored storage\n%!";
  let root_st = { zh; ctx; names } in
  let state = State.create ~ops:root_ops ~init:root_st () in
  let server = Tiny_httpd.create ~addr:"127.0.0.1" ~port:!port () in
  Tiny_httpd_camlzip.setup server;
  Server.add_route server state;
  Printf.printf "listening on http://127.0.0.1:%d/hx_inspect/\n%!" !port;
  match Tiny_httpd.run server with
  | Ok () -> ()
  | Error e ->
    Tiny_httpd.Server.stop server;
    raise e
  | exception e ->
    Tiny_httpd.Server.stop server;
    raise e
