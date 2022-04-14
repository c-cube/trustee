
type ctx = {
  filename: string;
  input: Loc_input.t;
  index: Line_index.t lazy_t;
}

let create ~filename str : ctx =
  { filename; input=Loc_input.string str;
    index=lazy (Line_index.of_string str);
  }

let create_file ~filename : ctx =
  { filename; input=Loc_input.file filename;
    index=lazy (Line_index.of_file filename);
  }

type t = int [@@deriving show]

let none : t = 0

let() = assert (Sys.int_size = 63)
let n_bits_offset = 31
let n_bits_len = Sys.int_size - n_bits_offset

let equal : t -> t -> bool = (=)

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

let add_offset ~off self =
  let off1, off2 = offsets self in
  mk_ (off+off1) (off+off2)

let contains self ~off:p : bool =
  let o1, o2 = offsets self in
  o1 <= p && p <= o2

let union a b =
  let a1, a2 = offsets a in
  let b1, b2 = offsets b in
  mk_ (min a1 b1) (max a2 b2)

let union_l a ~f l = List.fold_left (fun l x -> union l (f x)) a l

let of_lex_pos ~ctx:_ctx p1 p2 : t =
  let open Lexing in
  let off1 = p1.pos_cnum in
  let off2 = max off1 (p2.pos_cnum-1) in (* offset is one past end of token *)
  mk_ off1 off2

let of_lexbuf ~ctx (buf:Lexing.lexbuf) : t =
  let open Lexing in
  of_lex_pos ~ctx buf.lex_start_p buf.lex_curr_p

let tr_offset ctx off : int * int =
  let lazy index = ctx.index in
  Line_index.line_col_of_offset index ~off

let offset_of_pos ~ctx (pos:Position.t) : int =
  let lazy index = ctx.index in
  Line_index.find_offset index ~line:(Position.line pos) ~col:(Position.col pos)

let make_pos ~ctx p1 p2 : t =
  let off1 = offset_of_pos ~ctx p1 in
  let off2 = offset_of_pos ~ctx p2 in
  make ~ctx ~off1 ~off2

let pos_of_offset ~ctx off : Position.t =
  let line, col = tr_offset ctx off in
  Position.make ~line ~col

let positions ~ctx self =
  let off1, off2 = offsets self in
  pos_of_offset ~ctx off1, pos_of_offset ~ctx off2

let tr_position ~ctx ~left ~offset : Lexing.position =
  let line, col = tr_offset ctx offset in
  {Lexing.pos_fname=ctx.filename;
   pos_lnum=line;
   pos_cnum=offset + (if left then 0 else 1);
   pos_bol=offset - col;
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
