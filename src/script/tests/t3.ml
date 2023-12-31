module K = Kernel

let () =
  Printexc.register_printer (function
    | Error.E e -> Some (Error.show e)
    | _ -> None)

let s =
  {|

// naive fib
fn fib(n) {
  if n <= 2 {
    1
  } else {
    fib(n - 1) + fib(n - 2)
  }
}

// TODO: arrays + map with a closure

"fib 5";
fib(5);
fib(6);

"fib 12";
fib(12);

"fib 24";
fib(24);

|}

let ast =
  match parse_top_str ~filename:"t3" s with
  | Ok l -> l
  | Error e ->
    Format.printf "error: %a@." Error.pp e;
    []
;;

Format.printf "ast: %a@." Ast.pp_top ast

let ctx = K.Ctx.create ()

(* compile *)

let _env, stanzas = Compile.compile_l Compile.Env.empty ast;;

Format.printf "@[<2>compiled stanzas:@ %a@]@."
  (Fmt.Dump.list VM.Stanza.debug)
  stanzas

(* evaluate *)

let debug_hook vm i = ()
  (*
  ()
  Fmt.eprintf "@[<2>exec `%a`@ in %a@]@." VM.Instr.pp i VM.dump vm
        *)
  [@@ocaml.warning "-27"]
;;

try List.iter (VM.eval_stanza_pp ~debug_hook ctx) stanzas with _ -> ()

let rec fib n =
  if n <= 2 then
    1
  else
    fib (n - 1) + fib (n - 2)

let () =
  Fmt.printf "expected fib(5) = %d@." (fib 5);
  Fmt.printf "expected fib(12) = %d@." (fib 12);
  Fmt.printf "expected fib(24) = %d@." (fib 24);
  ()
