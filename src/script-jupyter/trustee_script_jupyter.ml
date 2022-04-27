
module Sc = Trustee_script
module JK = Jupyter_kernel
open Lwt.Infix
open Lwt.Syntax

type html = Tiny_httpd_html.elt

module Make() = struct
  module K = Trustee_core.Kernel
  module VM = Trustee_core.VM
  module H = Tiny_httpd_html

  let ctx = K.Ctx.create()

  let env_ref = ref Sc.Compile.Env.empty

  let render_eff (eff:VM.Eval_effect.t) : html =
    let open H in
    pre [][txtf "%a" VM.Eval_effect.pp eff]
    (* FIXME
    match eff with
    | VM.Eval_effect.Eff_declare (_, _) -> _
    | VM.Eval_effect.Eff_define (_, _) -> _
    | VM.Eval_effect.Eff_print_val _ -> _
    | VM.Eval_effect.Eff_prove (_, _, _) -> _
    | VM.Eval_effect.Eff_define_thunk (_, _) -> _
    | VM.Eval_effect.Eff_define_chunk (_, _) -> _
    | VM.Eval_effect.Eff_print_error _ -> _
       *)

  let exec ~count (str:string) : _ Lwt.t =
    match
      let filename = Printf.sprintf "cell %d" count in
      let st_l = Sc.parse_top_str_exn ~filename str in
      let env, stz_l = Sc.Compile.compile_l !env_ref st_l in
      env_ref := env;
      CCList.flat_map (VM.eval_stanza ctx) stz_l
    with
    | eff_l ->

      let mime =
        let html =
          List.map (fun eff ->
              let content = render_eff eff |> H.to_string in
              JK.Client.{
                mime_type= "text/html";
                mime_content=content;
                mime_b64= false;


              }
            ) eff_l
        in
        JK.Client.Kernel.Mime html
      in

      let has_err =
        List.exists
          (function VM.Eval_effect.Eff_print_error _ -> true | _ -> false)
          eff_l in
      let msg = if has_err then (Some "error") else None in
      let res = {
        JK.Client.Kernel.msg; actions=[mime];
      } in
      Lwt.return (Ok res)

    | exception e ->
      Lwt.return_error (Printexc.to_string e)

  let kernel =
    JK.Client.Kernel.make
      ~codemirror_mode:"javascript"
      ~file_extension:"trsc"
      ~language_version:[0;1]
      ~language:"trustee_script"
      ~exec
      ()
end

let main () : unit Lwt.t =
  let module M = Make() in
  let config = JK.Client_main.mk_config ~usage:"<usage>" () in
  JK.Client_main.main ~config ~kernel:M.kernel


let () =
  Lwt_main.run (main())
