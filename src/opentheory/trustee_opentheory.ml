(** {1 OpenTheory library}

    Support for parsing {{:http://www.gilith.com/opentheory/} opentheory}
    articles and theories. *)

module Common_ = Common_
module Name = Name
module Article = Article
module VM = VM
module Thy_file = Thy_file
module Idx = Idx
module Interp_file = Interp_file
module Util = Util
module Eval = Eval
module Logger = Logger
module Proof_zip = Proof_zip

(* Print GC stats on exit, useful for tracking memory usage of the opentheory binary. *)
let () = at_exit (fun () -> Gc.print_stat stderr)
