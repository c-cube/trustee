
(* generate some code for the VM instructions *)

let pf = Printf.printf
type arg =
  | Int
  | Bool

type doc=string

let instrs: (string*arg list*doc) list = [
  "nop", [], "( -- ) Do nothing";
  "call", [], "(chunk -- ) Pop and call the chunk or primitive that is on top of the stack";
  "ret", [], "( -- ) Return from current chunk";
  "dup", [], "(a -- a a) drop value on top of stack, discarding it";
  "drop", [], "(a -- ) drop value on top of stack, discarding it";
  "exch", [], "(a b -- b a) exchange the two top values of the stack";
  "extract", [Int], "(vs -- vs vs[-i]) extract <i>-th value, where 0 is top of the stack. `extract 0` is `dup`.";
  "rstore", [Int], "(x -- ) Pop value and store it into register <i>";
  "rload", [Int], "( -- x) Load value from register <i> and push it onto stack";
  "lload", [Int], "( -- x) Load i-th local value of current chunk and push it onto stack";
  "int", [Int], "( -- i) Push integer <i> on the stack";
  "bool", [Bool], "( -- b) Push boolean <b> on the stack";
  "nil", [], "( -- nil) Push nil on the stack";
  "not", [], "(a -- not(a)) Negate top value";
  "add", [], "(a b -- a+b) Pop two integer values, adds them";
  "add1", [], "(a -- a+1) Increment integer on top of stack";
  "sub", [], "(a b -- a-b) Pop two integer values, subtract them";
  "sub1", [], "(a -- a-1) Decrement integer on top of stack";
  "mult", [], "(a b -- a*b) Pop two integer values, multiply them";
  "eq", [], "(a b -- ) Pop two values; push boolean (a==b)";
  "lt", [], "(a b -- ) Pop two integer values; push boolean (a < b)";
  "leq", [], "(a b -- ) Pop two integer values; push boolean (a <= b)";
  "jif", [Int], "(bool -- ) Pop a boolean; if true, then set IP=<offset>";
  "jifn", [Int], "(bool -- ) Pop a boolean; if false, then set IP=<offset>";
  "jmp", [Int], "( -- ) Set IP=<offset> unconditionally";
  "memenv", [], "(str -- bool) Pop a string, returns `true` iff this name is bound in env";
  "getenv", [], "(str -- v) Pop a string, returns the value with this name in env. Fails if not present";
  "qenv", [], "(str -- v bool) Pop a string, returns `v, true` if `v` is the value with this name in env, `nil, false` otherwise.";
]

let emit_ty (name,args,doc) =
  pf "| %s" (String.capitalize_ascii name);
  let nargs = List.length args in
  if nargs=1 then pf " of ";
  if nargs>1 then pf " of (";
  List.iteri (fun i ty ->
      if i>0 then pf " * ";
      match ty with Int -> pf "int" | Bool -> pf "bool")
    args;
  if nargs>1 then pf ")";
  pf " (** %s *)" doc;
  pf "\n"

let emit_pp (name,args,doc) =
  pf "| %s" (String.capitalize_ascii name);
  let nargs = List.length args in
  if nargs=1 then pf " ";
  if nargs>1 then pf " (";
  List.iteri (fun i _ty ->
      if i>0 then pf ", ";
      pf "x%d" i)
    args;
  if nargs>1 then pf ")";
  if nargs=0 then pf {| -> Format.fprintf out "%s"|} name
  else (
    pf {| -> Format.fprintf out "(%s|} name;
    List.iteri (fun _i ty ->
        pf " ";
        match ty with
        | Int -> pf "%%d" | Bool -> pf "%%b") args;
    pf {|)"|};
    List.iteri (fun i _ -> pf "x%d" i) args;
  );
  pf "\n"

let () =
  pf "type t =\n";
  List.iter emit_ty instrs;
  pf "\n";
  pf "let pp out (i:t) : unit = match i with\n";
  List.iter emit_pp instrs;

