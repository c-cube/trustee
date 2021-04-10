
open Sigs
module P = Position

type t = {
  file: string;
  start: Position.t;
  end_: Position.t;
}

let pp out (self:t) : unit =
  if self.start.P.line = self.end_.P.line then (
    Fmt.fprintf out "%d:%d-%d" self.start.P.line self.start.P.col self.end_.P.col
  ) else (
    Fmt.fprintf out "%d:%d-%d:%d"
      self.start.P.line self.start.P.col self.end_.P.line self.end_.P.col
  )
let to_string = Fmt.to_string pp

let pp_opt out = function
  | None -> Format.fprintf out "<no location>"
  | Some pos -> pp out pos

let none : t = {file=""; start=P.none; end_=P.none}
let single ?(file="") p = {file; start=p; end_=p}

let merge a b = {file=a.file; start=P.min a.start b.start; end_=P.max a.end_ b.end_}
let contains self p : bool =
  P.leq self.start p && P.leq p self.end_

let mk file start_line start_column stop_line stop_column =
  let start = P.make ~line:start_line ~col:start_column in
  let end_ = P.make ~line:stop_line ~col:stop_column in
  { file; start; end_ }

let mk_pair file (a,b)(c,d) = mk file a b c d

module Infix = struct
  let (++) = merge
end
include Infix

let set_file buf filename =
  let open Lexing in
  buf.lex_curr_p <- {buf.lex_curr_p with pos_fname=filename;};
  ()

let get_file buf =
  let open Lexing in
  buf.lex_curr_p.pos_fname

let of_lexbuf lexbuf =
  let start = Lexing.lexeme_start_p lexbuf in
  let end_ = Lexing.lexeme_end_p lexbuf in
  let s_l = start.Lexing.pos_lnum in
  let s_c = start.Lexing.pos_cnum - start.Lexing.pos_bol in
  let e_l = end_.Lexing.pos_lnum in
  let e_c = end_.Lexing.pos_cnum - end_.Lexing.pos_bol in
  let file = get_file lexbuf in
  mk file s_l s_c e_l e_c
