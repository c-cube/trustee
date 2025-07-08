(** S-expressions with locations *)

open Common_

type t = {
  loc: Loc.t;
  view: view;
}

and view =
  | Atom of string
  | List of t list
  | Bracket_list of t list
  | Brace_list of t list
  | Quoted_string of string
  | Dollar of string
  | Error of Error.t

type sexp = t

let mk ~loc view : t = { loc; view }
let atom ~loc s : t = mk ~loc (Atom s)
let list ~loc s : t = mk ~loc (List s)
let bracket_list ~loc s : t = mk ~loc (Bracket_list s)
let brace_list ~loc s : t = mk ~loc (Brace_list s)
let dollar ~loc s : t = mk ~loc (Dollar s)
let quoted_str ~loc s : t = mk ~loc (Quoted_string s)
let error ~loc s : t = mk ~loc (Error s)

module PP = struct
  let rec pp out (self : t) : unit =
    match self.view with
    | Atom s -> Fmt.string out s
    | Dollar s -> Fmt.fprintf out "$%s$" s
    | Quoted_string s -> Fmt.fprintf out "%S" s
    | Bracket_list l ->
      Format.fprintf out "[@[<hov>";
      List.iteri
        (fun i e ->
          if i > 0 then Fmt.fprintf out "@ ";
          pp out e)
        l;
      Format.fprintf out "@]]"
    | Brace_list l ->
      Format.fprintf out "{@[<hv>";
      List.iteri
        (fun i e ->
          if i > 0 then Fmt.fprintf out "@ ";
          pp out e)
        l;
      Format.fprintf out "@]}"
    | List [] -> Fmt.string out "()"
    | List [ x ] -> Fmt.fprintf out "@[<hov2>(%a)@]" pp x
    | List l ->
      Format.fprintf out "@[<hov1>(";
      List.iteri
        (fun i t' ->
          if i > 0 then Format.fprintf out "@ ";
          pp out t')
        l;
      Format.fprintf out ")@]"
    | Error e -> Fmt.fprintf out "(@[error@ %a@])" Error.pp e
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

  let create ~filename (str : string) : t =
    let buf = Lexing.from_string ~with_positions:true str in
    { buf; ctx = Loc.LL.create ~filename str; cur_tok = None }

  let update_cur self : unit =
    if self.cur_tok == None then (
      (* fetch token *)
      let tok = L.token self.buf in
      self.cur_tok <- Some tok
    )

  let[@inline] cur (self : t) : L.token =
    update_cur self;
    match self.cur_tok with
    | Some t -> t
    | None -> assert false

  let[@inline] consume t = t.cur_tok <- None

  exception E_end
  exception E_error of Loc.t * Error.t

  let[@inline] loc_ (self : t) : Loc.t =
    let lloc = Loc.LL.of_lexbuf ~ctx:self.ctx self.buf in
    Loc.make ~ctx:self.ctx lloc

  type delim =
    | D_paren
    | D_bracket
    | D_brace

  type nesting = delim list

  (* error recovery: get out of the layers of open '(' and '[' *)
  let rec recover_err_ (self : t) (n : nesting) =
    match cur self, n with
    | L.EOI, _ -> ()
    | _, [] -> ()
    | (L.ATOM _ | L.QUOTED_STR _ | L.DOLLAR_STR _), _ ->
      consume self;
      recover_err_ self n
    | L.LPAREN, _ ->
      consume self;
      recover_err_ self (D_paren :: n)
    | L.LBRACKET, _ ->
      consume self;
      recover_err_ self (D_bracket :: n)
    | L.LBRACE, _ ->
      consume self;
      recover_err_ self (D_brace :: n)
    | L.RPAREN, D_paren :: n'
    | L.RBRACKET, D_bracket :: n'
    | L.RBRACE, D_brace :: n' ->
      consume self;
      recover_err_ self n'
    | L.RPAREN, _ :: D_paren :: n'
    | L.RBRACKET, _ :: D_bracket :: n'
    | L.RBRACE, _ :: D_brace :: n' ->
      (* assume we close the surrouding delim because clearly
         it doesn't match the first one *)
      consume self;
      recover_err_ self n'
    | (L.RPAREN | L.RBRACKET | L.RBRACE), _ ->
      consume self;
      recover_err_ self n

  let parse1 (self : t) =
    let open Lexing in
    let nesting = ref [] in

    (* parse an expression, at [depth] levels of list nesting *)
    let rec expr () =
      update_cur self;
      (* before using [loc_] *)
      let loc1 = loc_ self in
      match cur self with
      | L.EOI ->
        if !nesting = [] then
          raise_notrace E_end
        else (
          let err =
            Error.make ~loc:loc1
              "unexpected end of input while parsing S-expression"
          in
          raise (E_error (loc1, err))
        )
      | L.ATOM s ->
        consume self;
        atom ~loc:loc1 s
      | L.DOLLAR_STR (p1, p2, s) ->
        consume self;
        (* use p1 and p2 to specify the actual location *)
        let lloc = Loc.LL.of_lex_pos ~ctx:self.ctx p1 p2 in
        let loc = Loc.make ~ctx:self.ctx lloc in
        dollar ~loc s
      | L.QUOTED_STR s ->
        consume self;
        quoted_str ~loc:loc1 s
      | L.LPAREN ->
        consume self;
        nesting := D_paren :: !nesting;
        p_list ~loc1 []
      | L.LBRACKET ->
        consume self;
        nesting := D_bracket :: !nesting;
        p_list ~loc1 []
      | L.LBRACE ->
        consume self;
        nesting := D_brace :: !nesting;
        p_list ~loc1 []
      | L.RPAREN ->
        consume self;
        let err =
          Error.make ~loc:loc1 "unexpected ')' when parsing a S-expression"
        in
        raise_notrace (E_error (loc1, err))
      | L.RBRACKET ->
        consume self;
        let err =
          Error.make ~loc:loc1 "unexpected ']' when parsing a S-expression"
        in
        raise_notrace (E_error (loc1, err))
      | L.RBRACE ->
        consume self;
        let err =
          Error.make ~loc:loc1 "unexpected '}' when parsing a S-expression"
        in
        raise_notrace (E_error (loc1, err))
    and p_list ~loc1 acc =
      match cur self, !nesting with
      | L.RPAREN, D_paren :: n' ->
        nesting := n';
        consume self;
        let loc = loc1 ++ loc_ self in
        list ~loc @@ List.rev acc
      | L.RBRACKET, D_bracket :: n' ->
        nesting := n';
        consume self;
        let loc = loc1 ++ loc_ self in
        bracket_list ~loc @@ List.rev acc
      | L.RBRACE, D_brace :: n' ->
        nesting := n';
        consume self;
        let loc = loc1 ++ loc_ self in
        brace_list ~loc @@ List.rev acc
      | (L.RPAREN | L.RBRACKET | L.RBRACE), _ ->
        let loc = loc_ self in
        consume self;
        let err = Error.make ~loc "invalid closing delimiter" in
        raise (E_error (loc, err))
      | ( ( L.LPAREN | L.LBRACKET | L.LBRACE | L.ATOM _ | L.QUOTED_STR _
          | L.DOLLAR_STR _ ),
          _ ) ->
        let sub = expr () in
        p_list ~loc1 (sub :: acc)
      | L.EOI, _ ->
        let loc = loc_ self in
        let err =
          Error.make ~loc "unexpected end of input while parsing a list"
        in
        raise (E_error (loc, err))
    in

    try
      let e = expr () in
      Some e
    with
    | E_end -> None
    | E_error (loc, err) ->
      recover_err_ self !nesting;
      (* reify error *)
      let s = error ~loc err in
      Some s

  let parse self : _ list =
    let rec loop acc =
      match parse1 self with
      | None -> List.rev acc
      | Some s -> loop (s :: acc)
    in
    loop []
end

let of_string ~filename s =
  let p = Parse.create ~filename s in
  Parse.parse1 p

let of_string_l ~filename s =
  let p = Parse.create ~filename s in
  Parse.parse p
