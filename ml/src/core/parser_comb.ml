
(* This file is free software. See file "license" for more details. *)

(** {1 Parsing Combinators} *)

open Sigs

let spf = Printf.sprintf

type position = Position.t
type offset = int

type error = {
  offset: offset;
  pos: position;
  msg: string;
  parsing: string list;
}
type state = {
  src: string; (* the input *)
  i: offset; (* offset in [str] *)
  lnum : int; (* line number *)
  cnum : int; (* Column number *)
  saved_errors: error list ref;
}

type 'a or_error = ('a, error) result

exception Parse_error of error

module State = struct
  type t = state
  let create src : t = {src; i=0; lnum=1; cnum=1; saved_errors=ref [] }
  let pos self : position = {Position.line=self.lnum; col=self.cnum}
end

module Err = struct
  type t = error

  let pp out (self:t) : unit =
    let pp_parsing out = function
      | [] -> ()
      | l ->
        Fmt.fprintf out "@ while parsing %a"
          (pp_list ~sep:" in " Fmt.string) l
    in
    Format.fprintf out "@[%s@ at %a%a@]"
      self.msg Position.pp self.pos pp_parsing self.parsing

  let to_string = Fmt.to_string pp
end

let char_equal : char -> char -> bool = (==)
let string_equal = CCString.equal

let () = Printexc.register_printer
    (function
      | Parse_error e -> Some (Fmt.to_string Err.pp e)
      | _ -> None)

let[@inline] is_done st = st.i >= String.length st.src
let[@inline] cur st = String.get st.src st.i

type 'a t = {
  p: 'b. state -> ok:(state -> 'a -> 'b) -> err:(error -> 'b) -> 'b;
} [@@unboxed]
(** Takes the input and two continuations:

    - [ok] to call with the result when it's done
    - [err] to call when the parser met an error
    *)

let mk_error_ (self:state) msg : error =
  { offset=self.i; pos=State.pos self; msg; parsing=[]; }

let mk_error_eof_ self : error =
  mk_error_ self "unexpected end of input"

let next (self:state) : state * char =
  assert (not (is_done self));
  let c = cur self in
  let state =
    if char_equal c '\n' then (
      {self with
       i=self.i + 1;
       lnum=self.lnum +1;
       cnum=1;
      }
    ) else (
      {self with cnum=self.cnum+1; i=self.i+1;}
    ) in
  state, c

let[@inline] return (x:'a) : 'a t = {p=fun _st ~ok ~err:_ -> ok _st x}
let pure = return
let[@inline] (>>=) (x:'a t) (f:'a -> 'b t) : 'b t =
  {p=fun st ~ok ~err -> x.p st ~ok:(fun st x -> (f x).p st ~ok ~err) ~err}
let[@inline] (<*>) (f:('a -> 'b) t) (x:'a t) : 'b t =
  {p=fun st ~ok ~err ->
      f.p st ~ok:(fun st f -> x.p st ~ok:(fun st x -> ok st (f x)) ~err) ~err}
let[@inline] (<* ) (x:'a t) (y:_ t) : 'a t =
  {p=fun st ~ok ~err ->
      x.p st ~ok:(fun st x -> y.p st ~ok:(fun st _ -> ok st x) ~err) ~err}
let[@inline] ( *>) (x:_ t) (y:'a t) : 'a t =
  {p=fun st ~ok ~err ->
      x.p st ~ok:(fun st _ -> y.p st ~ok ~err) ~err}

let[@inline] product (x:'a t)(y:'b t) : _ t =
  {p=fun st ~ok ~err ->
      x.p st ~err
        ~ok:(fun st x ->
            y.p st ~err ~ok:(fun st y -> ok st (x,y)))
  }

let[@inline] map f x =
  {p=fun st ~ok ~err ->
      x.p st ~err ~ok:(fun st x ->
          ok st (f x))}
let[@inline] (>|=) x f = map f x
let[@inline] map2 f x y =
  {p=fun st ~ok ~err ->
      x.p st ~err ~ok:(fun st x ->
          y.p st ~err ~ok:(fun st y ->
              ok st (f x y)))}

let[@inline] map3 f x y z =
  {p=fun st ~ok ~err ->
      x.p st ~err ~ok:(fun st x ->
          y.p st ~err ~ok:(fun st y ->
              z.p st ~err ~ok:(fun st z ->
                  ok st (f x y z))))}

let eoi =
  {p=fun st ~ok ~err ->
      if is_done st
      then ok st ()
      else err (mk_error_ st "expected end of input")}

let try_bind x ~ok:tr_ok ~err:tr_err =
  {p=fun st ~ok ~err ->
      x.p st
        ~ok:(fun st x -> (tr_ok x).p st ~ok ~err)
        ~err:(fun e -> (tr_err e).p st ~ok ~err)
  }

let fail msg = {p=fun st ~ok:_ ~err -> err (mk_error_ st msg)}
let failf msg = Format.kasprintf fail msg

let save_error e =
  {p=fun st ~ok ~err:_ ->
      st.saved_errors := e :: !(st.saved_errors);
      ok st ()
  }

let parsing s x =
  {p=fun st ~ok ~err ->
      x.p st ~ok
        ~err:(fun e -> err {e with parsing=s::e.parsing})
  }

let nop = {p=fun st ~ok ~err:_ -> ok st ()}

let char =
  {p=fun st ~ok ~err ->
      if is_done st then err (mk_error_eof_ st)
      else (
        let st, c = next st in
        ok st c
      )
  }

let char_exact c =
  {p=fun st ~ok ~err ->
      if is_done st then err (mk_error_eof_ st)
      else (
        let st, c' = next st in
        if char_equal c c' then ok st c
        else err (mk_error_ st (spf "expected '%c'" c))
      )
  }

let char_if ?msg p =
  {p=fun st ~ok ~err ->
      if is_done st then err (mk_error_eof_ st)
      else (
        let st, c = next st in
        if p c then ok st c
        else
          let msg = match msg with
            | Some m -> m
            | None -> spf "invalid char '%c'" c
          in
          err (mk_error_ st msg)
      )
  }

let chars_if_len ?msg (len:int) p =
  {p=fun st ~ok ~err ->
      let i = st.i in
      if i+len > String.length st.src then (
        let msg = match msg with
          | Some m -> m
          | None -> spf "expected %d chars" len
        in
        err (mk_error_ st msg)
      ) else (
        try
          for j=0 to len-1 do
            if not (p (String.get st.src (i+j))) then raise_notrace Exit
          done;
          let st = {st with i=st.i + len; cnum=st.cnum+len} in
          ok st (String.sub st.src i len)
        with Exit ->
          let msg = match msg with
            | Some m -> m
            | None -> spf "string of length %d is invalid" len
          in
          err (mk_error_ st msg)
      )
  }

let chars_if p =
  {p=fun st ~ok ~err:_ ->
    let i = st.i in
    let len = ref 0 in
    while i + !len < String.length st.src && p (String.get st.src (i+ !len)) do
      incr len;
    done;
    let st = {st with i=i + !len; cnum=st.cnum + !len} in
    ok st (String.sub st.src i !len)
  }

let chars1_if ?msg p =
  let p' = chars_if p in
  {p=fun st ~ok ~err ->
    p'.p st
      ~ok:(fun st s ->
        if string_equal s "" then (
          let msg = match msg with
            | Some m -> m
            | None -> "needed non-empty sequence of chars"
          in
          err (mk_error_ st msg)
        ) else ok st s)
      ~err
  }

let skip_chars p =
  {p=fun st ~ok ~err:_ ->
      let i = st.i in
      let len = ref 0 in
      while i + !len < String.length st.src && p (String.get st.src (i+ !len)) do
        incr len
      done;
      let st = {st with i=i + !len; cnum=st.cnum + !len} in
      ok st ()
  }

let is_alpha = function
  | 'a' .. 'z' | 'A' .. 'Z' -> true
  | _ -> false
let is_num = function '0' .. '9' -> true | _ -> false
let is_alpha_num = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true
  | _ -> false
let is_space = function ' ' | '\t' -> true | _ -> false
let is_white = function ' ' | '\t' | '\n' -> true | _ -> false

let space = char_if is_space
let white = char_if is_white

let endline = char_exact '\n'

let skip_space = skip_chars is_space
let skip_white = skip_chars is_white

let (<|>) (x:'a t) (y:'a t) : 'a t =
  {p=fun st ~ok ~err ->
    x.p st ~ok
      ~err:(fun _e -> y.p st ~ok ~err)
  }

let if_
  : type a b. a t -> (a -> b t) -> b t -> b t
  = fun x ptrue pfalse ->
  {p=fun st ~ok ~err ->
      x.p st
        ~ok:(fun st x -> (ptrue x).p st ~ok ~err)
        ~err:(fun _ -> pfalse.p st ~ok ~err)
  }

let cond l else_ : _ t =
  {p=fun st ~ok ~err ->
      let rec aux l = match l with
        | [] -> else_.p st ~ok ~err (* fallback *)
        | (c_i, br_i) :: tl ->
          c_i.p st
            ~ok:(fun st _ -> br_i.p st ~ok ~err)
            ~err:(fun _ -> aux tl)
      in
      aux l
  }

let suspend f =
  let p' = lazy (f ()) in
  {p=fun st ~ok ~err -> (Lazy.force p').p st ~ok ~err}

let (<?>) (x:'a t) (msg:string) : 'a t =
  {p=fun st ~ok ~err ->
      x.p st ~ok
        ~err:(fun e ->
          let e = {
            e with
            pos={Position.line=st.lnum; col=st.cnum};
            msg;
          } in
          err e
        )
  }

let string_exact s : unit t =
  {p=fun st ~ok ~err ->
      let len = String.length s in
      let i = st.i in
      if i + len > String.length st.src then (
        err (mk_error_ st (spf "expected '%s'" s))
      ) else (
        let is_eq = ref true in
        for j = 0 to len-1 do
          is_eq := !is_eq && String.get st.src (i+j) = String.get s j
        done;
        if !is_eq then (
          let st = {st with i=st.i + len; cnum=st.cnum+len} in
          ok st ()
        ) else (
          err (mk_error_ st (spf "expected '%s'" s))
        )
      )
  }

let many (x:'a t) : 'a list t =
  {p=fun st ~ok ~err:_ ->
      let rec aux st acc =
        x.p st
          ~err:(fun _ -> ok st (List.rev acc))
          ~ok:(fun st x -> aux st (x::acc))
      in
      aux st []
  }

let many1 ?msg (x:'a t) : 'a list t =
  {p=fun st ~ok ~err ->
      let rec aux st acc =
        x.p st
          ~err:(fun _ ->
              match acc with
              | [] ->
                let msg = match msg with
                  | Some m -> m
                  | None -> "expected non-empty list"
                in
                err (mk_error_ st msg)
              | _ -> ok st (List.rev acc))
          ~ok:(fun st x -> aux st (x::acc))
      in
      aux st []
  }

let skip (p:_ t) : unit t =
  {p=fun st ~ok ~err:_ ->
      let rec aux st =
        p.p st ~err:(fun _ -> ok st ())
          ~ok:(fun st _ -> aux st)
      in
      aux st
  }

let sep_rec_ p ~by st ~ok acc =
  let rec aux st acc =
    p.p st
      ~ok:(fun st x ->
          let acc = x :: acc in
          by.p st
            ~ok:(fun st _ -> aux st acc)
            ~err:(fun _ ->
                ok st (List.rev acc)))
      ~err:(fun _ -> ok st (List.rev acc))
  in
  aux st acc

let sep ~by p =
  {p=fun st ~ok ~err:_ -> sep_rec_ p ~by st ~ok []}

let sep1 ~by p =
  {p=fun st ~ok ~err ->
      p.p st ~err
        ~ok:(fun st x ->
            by.p st ~err:(fun _ -> ok st [x])
              ~ok:(fun st _ -> sep_rec_ p ~by st ~ok [x]))
  }

let fix f : _ t =
  let rec pr = {
    p=fun st ~ok ~err ->
      (Lazy.force fpr).p st ~ok ~err
  } and fpr = lazy (f pr) in
  pr

let cur_pos = {
  p=fun st ~ok ~err:_ -> ok st (State.pos st)
}

let int =
  chars1_if ~msg:"expected int" (fun c -> is_num c || char_equal c '-')
  >>= fun s ->
  try return (int_of_string s)
  with Failure _ -> fail "expected an int"

let prepend_str_ c s = String.make 1 c ^ s

let[@specialise] ident_with_sym f : string t =
  map2 prepend_str_ (char_if is_alpha) (chars_if (fun c -> is_alpha_num c || f c))

let ident = ident_with_sym (fun c -> c = '_')

let list ?(start="[") ?(stop="]") ?sep:(sep_=";") p =
  parsing "list" @@ (
    (skip_white *> string_exact start) *>
    (sep
       ~by:(skip_white *> string_exact sep_)
       (skip_white *> p)
    ) <* (skip_white *> string_exact stop)
  )

let parse_exn (p:_ t) s =
  p.p (State.create s)
    ~ok:(fun _st x -> x)
    ~err:(fun e -> raise (Parse_error e))

let parse (p:_ t) s =
  p.p (State.create s)
    ~ok:(fun _st x -> Ok x)
    ~err:(fun e -> Error e)

let parse_with_errors (p:_ t) s =
  let st = State.create s in
  p.p st
    ~ok:(fun _st x -> Ok x, !(st.saved_errors))
    ~err:(fun e -> Error e, !(st.saved_errors))

module Infix = struct
  let (>|=) = (>|=)
  let (>>=) = (>>=)
  let (<*>) = (<*>)
  let (<* ) = (<* )
  let ( *>) = ( *>)
  let (<|>) = (<|>)
  let (<?>) = (<?>)
end

(*$inject
  module T = struct
    type tree = L of int | N of tree * tree
  end
  open T

  let mk_leaf x = L x
  let mk_node x y = N(x,y)

  let ptree = fix @@ fun self ->
    skip_space *>
    ( (char_exact '(' *> (pure mk_node <*> self <*> self) <* char_exact ')')
      <|>
      (int >|= mk_leaf) )

  let ptree' =
    parsing "tree" @@ fix @@ fun self ->
    skip_space *>
      cond [
        (char_exact '('),
        ((pure mk_node <*> self <*> self) <* char_exact ')');
      ]
      (int >|= mk_leaf)

  let rec pptree = function
    | N (a,b) -> Printf.sprintf "N (%s, %s)" (pptree a) (pptree b)
    | L x -> Printf.sprintf "L %d" x

  let errpptree = function
    | Ok x -> "Ok " ^ pptree x
    | Error s -> "Error " ^ Err.to_string s
*)

(*$= & ~printer:errpptree
  (Ok (N (L 1, N (L 2, L 3)))) \
    (parse ptree "(1 (2 3))" )
  (Ok (N (N (L 1, L 2), N (L 3, N (L 4, L 5))))) \
    (parse ptree "((1 2) (3 (4 5)))" )
  (Ok (N (N (L 1, L 2), N (L 3, N (L 4, N (N (L 3, L 2), N (L 21, N (L 2, L 5)))))))) \
    (parse ptree' "((1 2) (3 (4 ( ( 3 2) (21 (2 5))))))")
*)

(*$R
  let p =
    skip_white *> char_exact '(' *> skip_white *> int
    <* skip_white *> char_exact ')'
  in
  assert_equal (Ok 123) (parse p "(123 )");
  assert_equal (Ok 123) (parse p "   ( 123  )  ");
  assert_equal (Ok 123) (parse p "(123 )");
*)

(*$R
  let p = list ~sep:"," ident in
  let printer = function
    | Ok l -> "Ok " ^ CCFormat.(to_string (Dump.list Dump.string)) l
    | Error s -> "Error " ^ Err.to_string s
  in
  assert_equal ~printer
    (Ok ["abc"; "de"; "hello"; "world"])
    (parse p "[abc , de, hello ,world  ]");
*)

(*$inject
  let test_list n =
    let p = list ~sep:"," int in
    let l = CCList.(1 -- n) in
    let l_printed =
      CCFormat.(to_string @@ within "[" "]" @@ hovbox @@
                list ~sep:(return ",@,") int) l in
    let l' = parse_exn p l_printed in

    assert_equal ~printer:Q.Print.(list int) l l'
*)

(*$R
  test_list 30;
*)

(* more serious benchmark *)
(*$R
  test_list 300_000;
 *)

(*$R
  let open Infix in
  let parens p = char_exact '(' *> p <* char_exact ')' in
  let add = char_exact '+' *> return (+) in
  let sub = char_exact '-' *> return (-) in
  let mul = char_exact '*' *> return ( * ) in
  let div = char_exact '/' *> return ( / ) in
  let integer =
  chars1_if (function '0'..'9'->true|_->false) >|= int_of_string in

  let chainl1 e op =
  fix (fun r ->
    e >>= fun x -> (op <*> return x <*> r) <|> return x) in

  let expr : int t =
  fix (fun expr ->
    let factor = parens expr <|> integer in
    let term = chainl1 factor (mul <|> div) in
    chainl1 term (add <|> sub)) in

  assert_equal (Ok 6) (parse expr "4*1+2");
  assert_equal (Ok 12) (parse expr "4*(1+2)");
  ()
*)

(*$R
  let p0 = skip_white *> int in
  let p = (skip_white *> char_exact '(' *> many p0) <* (skip_white <* char_exact ')') in
  let printer =  CCFormat.(
      to_string @@
      map (CCResult.map_err Err.to_string) @@
      (Dump.result @@ Dump.list int)) in
  assert_equal ~printer
    (Ok [1;2;3]) (parse p "(1 2 3)");
  assert_equal ~printer
    (Ok [1;2; -30; 4]) (parse p "( 1 2    -30 4 )")
  *)

(*$=
  (parse_exn (list ~sep:"," int) "[1,2,3]") [1;2;3]
*)
