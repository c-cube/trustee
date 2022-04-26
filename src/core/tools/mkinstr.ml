
(* generate some code for the VM instructions *)

let pf = Printf.printf

(** Opcode argument *)
type op_arg =
  | Int
  | Bool

type doc=string

let instrs: (string*op_arg list*doc) list = [
  "nop", [], "( -- ) Do nothing";
  "call", [Int], "(<n values> chunk -- ) \
                  Pop and call the chunk or primitive that is on top of the stack \
                  with the top <n> values below it";
  "ret", [], "( -- ) Return values from current chunk (number determined by chunk arity)";
  "dup", [], "(a -- a a) drop value on top of stack, discarding it";
  "drop", [], "(a -- ) drop value on top of stack, discarding it";
  "exch", [], "(a b -- b a) exchange the two top values of the stack";
  "extract", [Int], "(vs -- vs vs[-i]) extract <i>-th value, where 0 is top of the stack.\n\
                     `extract 0` is `dup`.";
  "rstore", [Int], "(x -- ) Pop value and store it into register <i>";
  "rload", [Int], "( -- x) Load value from register <i> and push it onto stack";
  "lload", [Int], "( -- x) Load i-th local value of current chunk and push it onto stack";
  "int", [Int], "( -- i) Push integer <i> on the stack";
  "bool", [Bool], "( -- b) Push boolean <b> on the stack";
  "nil", [], "( -- nil) Push nil on the stack";
  "not", [], "(a -- not(a)) Negate top value";

  "acreate", [], "( -- arr) Create a new array.";
  "apush", [], "(arr x -- ) Pushes `x` onto the array.";
  "aget", [], "(arr i -- x) Gets `a[i]`.";
  "aset", [], "(arr i x -- ) Sets `a[i]` to `x`.";
  "alen", [], "(arr -- n) Gets the length of the array.";
  "aclear", [], "(arr -- ) Clear the array's content.";

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
  "tforce", [], "(th -- x) Evalutes thunk and pushes the value onto the stack";
  "curch", [], "( -- c) Pushes current thunk onto the stack";

  "type", [], "( -- type) Pushes the kind `type`.";
  "var", [], "(str ty -- var) Pop a string and a type, pushes a variable.";
  "vty", [], "(var -- ty) Pop a variable, pushes its type.";
  "tyarr", [], "(ty ty -- ty) Pops types `a` and `b, pushes `a -> b`.";
  "evar", [], "(var -- expr) Pop a name and a type, return variable.";
  "eapp", [], "(f e -- expr) Pop expressions `f` and `e`, pushes `f e`.";
  "elam", [], "(var expr -- expr) Pops variable `v` and body `e`, and pushes `\\v. e`.";
  "econst", [], "(c []ty -- expr) Pops constant and type arguments, pushes expression.";
  "econst0", [], "(c -- expr) Pops nullary constant, pushes expression.";
  "econst1", [], "(c ty -- expr) Pops unary constant and parameter, pushes expression.";
  "deapp", [], "(expr -- expr? expr? bool) Pops expression, returns `f a true` \
                if it's `f a`, pushes `nil nil false` otherwise.";
  "delam", [], "(expr -- var? expr? bool) Pops expression, returns `v bod true` \
                if it's `\\v.bod`, `nil nil false` otherwise.";
  "devar", [], "(expr -- var? bool) Pops expression, returns `v true` \
                if it's variable `v`, `nil false` otherwise.";
  "deconst", [], "(expr -- const? []ty? bool) Pops expression, returns \
                  `c args true` if it's `c` applied to arguments `args`; \
                  returns `nil nil false` otherwise..";
  "suem", [], "( -- subst) Pushes empty subst.";
  "subinde", [], "(subst v e -- subst) Binds var `v` to expression `e`.";
  "subindty", [], "(subst v ty -- subst) Binds var `v` to type `ty`.";

  "thabs", [], {|(th var -- th) Pops `|- t=u` and `v`, pushes `|- \v.t=\v.u`.|};
  "thcongr", [], "(th th -- th) Pops `|- f=g` and `|- a=b`, pushes `|- f a=g b`.";
  "thass", [], "(expr -- th) Pops `e`, pushes `e |- e`.";
  "thcut", [], "(th th -- th) Pops th2, th1, pushes `cut th1 th2`.";
  "threfl", [], "(e -- th) Pops `e`, pushes `|- e=e`.";
  "thsym", [], "(th -- th) Pops `|- a=b`, pushes `|- b=a`.";
  "thtrans", [], "(th th -- th) Pops th2, th1, pushes `trans th1 th2`.";
  "thbeq", [], "(th th -- th) Pops th2, th1, pushes `bool_eq th1 th2`.";
  "thbeqi", [], "(th th -- th) Pops th2, th1, pushes `bool_eq_intro th1 th2`.";
  "thbeta", [], {|(expr -- th) Pops `(\x. t) u`, pushes `|- (\x.t) u = t[x:=u]`.|};
  "thsubst", [], "(th subst -- th) Instantiate the theorem with the substitution.";
  "dth", [], "(th -- []expr expr) Pops `F |- e`, pushes array `F` and conclusion `e`.";
  "stopexec", [], "( -- ) Stop execution of this thunk.";
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
        | Int -> pf "%%d"
        | Bool -> pf "%%b"
      ) args;
    pf {|)"|};
    List.iteri (fun i ty ->
        match ty with
        | Int | Bool -> pf "x%d" i
      ) args;
  );
  pf "\n"

let emit_name = function
  | "type" -> "type_"
  | s -> s

let emit_mk_sig (name,args,doc) =
  pf "\n  (** %s *)\n" doc;
  pf "  val %s : " @@ emit_name name;
  List.iter (fun ty ->
      match ty with
      | Int -> pf "int -> ";
      | Bool -> pf "bool -> ";
    )
    args;
  pf "t\n";
  ()

let emit_mk (name,args,_doc) =
  pf "  let %s" (emit_name name);
  let n = List.length args in
  List.iteri (fun i ty ->
      pf " (x_%d : " i;
      match ty with
      | Int -> pf "int)";
      | Bool -> pf "bool)";
    )
    args;
  pf " : t = %s" (String.capitalize_ascii name);
  if n=0 then ()
  else if n=1 then pf " x_0"
  else (
    pf "("; List.iteri (fun i _ -> if i>0 then pf ","; pf "x_%d" i) args; pf ")"
  );
  pf "\n"

let () =
  pf "type t =\n";
  List.iter emit_ty instrs;
  pf "\n";
  pf "let pp out (i:t) : unit = match i with\n";
  List.iter emit_pp instrs;
  pf "\n";
  pf "(** Instruction builder *)\n";
  pf "module Build : sig\n";
  List.iter emit_mk_sig instrs;
  pf "end = struct\n";
  List.iter emit_mk instrs;
  pf "end\n";
  ()

