(** S-expressions with locations *)

open Common_

type t = {
  loc: Loc.t;
  view: view;
}
and view =
  | Atom of string
  | List of t list
  | Dollar of string
  | Error of Error.t

type sexp = t

let mk ~loc view : t = {loc;view}
let atom ~loc s : t = mk ~loc (Atom s)
let list ~loc s : t = mk ~loc (List s)
let dollar ~loc s : t = mk ~loc (Dollar s)
let error ~loc s : t = mk ~loc (Error s)

module PP = struct
  (* shall we escape the string because of one of its chars? *)
  let _must_escape s =
    try
      for i = 0 to String.length s - 1 do
        let c = String.unsafe_get s i in
        match c with
          | ' ' | ')' | '(' | '"' | ';' | '\\' | '\n' | '\t' | '\r' -> raise Exit
          | _ when Char.code c > 127 -> raise Exit  (* non-ascii *)
          | _ -> ()
      done;
      false
    with Exit -> true

  (* empty atoms must be escaped *)
  let _must_escape s = String.length s = 0 || _must_escape s

  let rec pp out (self:t) : unit =
    match self.view with
    | Atom s ->
          if _must_escape s then Format.fprintf out "\"%s\"" (String.escaped s)
          else Format.pp_print_string out s
    | Dollar s -> Fmt.fprintf out "$ %s $" s
    | List [] -> Format.pp_print_string out "()"
    | List [x] -> Format.fprintf out "@[<hov2>(%a)@]" pp x
    | List l ->
      Format.fprintf out "@[<hov1>(";
      List.iteri
        (fun i t' -> (if i > 0 then Format.fprintf out "@ "; pp out t'))
        l;
      Format.fprintf out ")@]"
    | Error e ->
      Fmt.fprintf out "<@[error@ %a@]>" Error.pp e
end

let pp = PP.pp
let to_string = Fmt.to_string pp

module Parse = struct
  module L = Sexp_lex
  open Loc.Infix

  type 'a parse_result =
    | Yield of 'a
    | Fail of Error.t
    | End

  type t = {
    ctx: Loc.LL.ctx;
    buf: Lexing.lexbuf;
    mutable cur_tok: L.token option; (* current token *)
  }

  let create ~filename (str:string) : t =
    let buf = Lexing.from_string ~with_positions:true str in
    { buf;
      ctx=Loc.LL.create ~filename str;
      cur_tok=None;
    }

  let[@inline] cur (self:t): L.token =
    match self.cur_tok with
    | Some t -> t
    | None ->
      (* fetch token *)
      let tok = L.token self.buf in
      self.cur_tok <- Some tok;
      tok

  let[@inline] consume t = t.cur_tok <- None

  exception E_end
  exception E_error of Loc.t * Error.t

  let[@inline] loc_ (self:t) : Loc.t =
    let lloc = Loc.LL.of_lexbuf ~ctx:self.ctx self.buf in
    Loc.make ~ctx:self.ctx lloc

  type nesting =
    | N_empty
    | N_paren of nesting
    | N_bracket of nesting

  (* error recovery: get out of the layers of open '(' and '[' *)
  let rec recover_err_ (self:t) (n:nesting) =
    match cur self, n with
    | L.EOI, _ -> ()
    | _, N_empty -> ()
    | (L.ATOM _ | L.DOLLAR_STR _), _ ->
      consume self; recover_err_ self n
    | L.LPAREN, _ -> consume self; recover_err_ self (N_paren n)
    | L.LBRACKET , _ -> consume self; recover_err_ self (N_bracket n)
    | L.RPAREN, N_paren n' -> consume self; recover_err_ self n'
    | L.RBRACKET, N_bracket n' -> consume self; recover_err_ self n'
    | (L.RPAREN | L.RBRACKET), _ ->
      consume self; recover_err_ self n


  let parse1 (self:t) =
    let open Lexing in

    let nesting = ref N_empty in

    (* parse an expression, at [depth] levels of list nesting *)
    let rec expr () =
      let loc1 = loc_ self in
      match cur self with
      | L.EOI ->
        if !nesting=N_empty then (
          raise_notrace E_end
        ) else (
          let err = Error.make ~loc:loc1
              "unexpected end of input while parsing S-expression" in
          raise (E_error (loc1, err))
        )
      | L.ATOM s ->
        consume self;
        atom ~loc:loc1 s

      | L.DOLLAR_STR s ->
        consume self;
        dollar ~loc:loc1 s

      | L.LPAREN ->
        consume self;
        nesting := N_paren !nesting;
        p_list ~loc1 []

      | L.LBRACKET ->
        consume self;
        nesting := N_bracket !nesting;
        p_list ~loc1 []

      | L.RPAREN ->
        let err = Error.make ~loc:loc1 "unexpected ')' when parsing a S-expression" in
        raise_notrace (E_error (loc1,err))
      | L.RBRACKET ->
        let err = Error.make ~loc:loc1 "unexpected ']' when parsing a S-expression" in
        raise_notrace (E_error (loc1,err))

    and p_list ~loc1 acc =
      match cur self, !nesting with
      | L.RPAREN, N_paren n' ->
        nesting := n';
        consume self;
        let loc = loc1 ++ loc_ self in
        list ~loc @@ List.rev acc

      | L.RBRACKET, N_bracket n' ->
        nesting := n';
        consume self;
        let loc = loc1 ++ loc_ self in
        list ~loc @@ List.rev acc

      | (L.RPAREN | L.RBRACKET), _ ->
        let loc = loc_ self in
        let err = Error.make ~loc "invalid closing delimiter" in
        raise (E_error (loc, err))

      | (L.LPAREN | L.LBRACKET | L.ATOM _ | L.DOLLAR_STR _), _ ->
        let sub = expr () in
        p_list ~loc1 (sub::acc)
      | L.EOI, _ ->
        let loc = loc_ self in
        let err = Error.make ~loc "unexpected end of input while parsing a list" in
        raise (E_error (loc, err))
    in

    try
      let e = expr() in
      Some e
    with
    | E_end -> None
    | E_error (loc, err) ->
      recover_err_ self !nesting;
      (* reify error *)
      let s = error ~loc err in
      Some s

  let parse self : _ list =
    let rec loop acc = match parse1 self with
      | None -> List.rev acc
      | Some s -> loop (s::acc)
    in
    loop []
end


let of_string ~filename s =
  let p = Parse.create ~filename s in
  Parse.parse1 p

let of_string_l ~filename s =
  let p = Parse.create ~filename s in
  Parse.parse p
