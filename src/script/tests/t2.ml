
module K = Kernel

let s = {|

fn fact(n) {
  var i = n;
  var res = 1;

  while i > 0 {
    res = res * i;
    i = i - 1;
  }
  res
}

fact(5);

|}

let ast = match parse_top_str ~filename:"t2" s with
  | Ok l -> l
  | Error e ->
    Format.printf "error: %a@." Error.pp e;
    [];;

Format.printf "ast: %a@." Ast.pp_top ast;;

let ctx = K.Ctx.create();;

(* compile *)

let _env, stanzas = Compile.compile_l Compile.Env.empty ast;;

Format.printf "@[<2>compiled stanzas:@ %a@]@." (Fmt.Dump.list VM.Stanza.debug) stanzas;;

(* evaluate *)

let debug_hook vm i =
  Fmt.eprintf "@[<2>exec `%a`@ in %a@]@." VM.Instr.pp i VM.dump vm;;

List.iter (VM.eval_stanza ~debug_hook ctx) stanzas;;
