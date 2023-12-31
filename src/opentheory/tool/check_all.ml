open Trustee_opentheory
open Common_

let check ~st ~names () : unit =
  Iter.iter
    (fun name ->
      match Eval.eval_theory st.St.eval name with
      | Ok _ -> ()
      | Error e -> Format.eprintf "error: %a" Trustee_core.Error.pp e)
    names;
  ()
