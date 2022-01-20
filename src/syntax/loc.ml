
module Fmt = CCFormat

type ctx = {
  str: string;
  filename: string;
  input: Loc_input.t;
  index: Line_index.t lazy_t;
}

let create ~filename str : ctx =
  { str; filename; input=Loc_input.string str;
    index=lazy (Line_index.of_string str);
  }

type t = int [@@deriving show]

let none : t = 0

let() = assert (Sys.int_size = 63)
let n_bits_offset = 31
let n_bits_len = Sys.int_size - n_bits_offset

let mk_ off1 off2 : t =
  assert (off2 >= off1);
  let len = off2 - off1 in
  assert (off1 < 1 lsl n_bits_offset);
  assert (len < 1 lsl n_bits_len);
  off1 lor (len lsl n_bits_offset)

let[@inline] make ~ctx:_ctx ~off1 ~off2 : t = mk_ off1 off2

let offsets self =
  let off1 = self land ((1 lsl n_bits_offset) - 1) in
  let len = self lsr n_bits_offset in
  let off2 = off1 + len in
  off1, off2

let union a b =
  let a1, a2 = offsets a in
  let b1, b2 = offsets b in
  mk_ (min a1 b1) (max a2 b2)

let of_lexbuf ~ctx:_ctx (buf:Lexing.lexbuf) : t =
  let open Lexing in
  let off1 = buf.lex_start_p.pos_cnum in
  let off2 = buf.lex_curr_p.pos_cnum in
  mk_ off1 off2

let tr_offset ctx off : int * int =
  let lazy index = ctx.index in
  Line_index.line_col_of_offset index ~off

let tr_position ~ctx ~left (p:int) : Lexing.position =
  let line, col = tr_offset ctx p in
  {Lexing.pos_fname=ctx.filename;
   pos_lnum=line;
   pos_cnum=p + (if left then 0 else 1);
   pos_bol=p - col;
  }

let line_cols_ ~ctx self =
  let off1, off2 = offsets self in
  let l1,c1 = tr_offset ctx off1 in
  let l2,c2 = tr_offset ctx off2 in
  l1,c1,l2,c2

module Infix = struct
  let (++) = union
end
include Infix

let pp ~ctx out (self:t) =
  if self == none then ()
  else (
    let l1, c1, l2, c2 = line_cols_ ~ctx self in
    if l1=l2 then (
      Format.fprintf out "in file '%s', line %d columns %d..%d"
        ctx.filename l1 c1 c2
    ) else (
      Format.fprintf out "in file '%s', line %d col %d to line %d col %d"
        ctx.filename l1 c1 l2 c2
    )
  )
