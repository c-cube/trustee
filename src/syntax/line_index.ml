
module Vec = CCVector

(* a list of offsets of newlines *)
type t = {
  lines: int array;
  size: int; (* total length *)
}

let of_string (s:string) : t =
  let lines = Vec.create() in
  Vec.push lines 0; (* first line is free *)
  let size = String.length s in
  let i = ref 0 in
  while !i < size do
    match String.index_from_opt s !i '\n' with
    | None -> i := size
    | Some j ->
      Vec.push lines j;
      i := j+1;
  done;
  let lines = Vec.to_array lines in
  { lines; size; }

let line_col_of_offset self ~off : int * int =
  (* binary search *)
  let low = ref 0 in
  let high = ref (Array.length self.lines) in
  let continue = ref true in
  while !continue && !low < !high do
    let middle = !low / 2 + !high / 2 in
    let off_middle = self.lines.(middle) in

    if off_middle <= off then (
      if middle + 1 = Array.length self.lines ||
         self.lines.(middle + 1) > off then (
        (* found the range *)
        low := middle;
        continue := false;
      ) else (
        low := middle + 1;
      )
    ) else (
      high := middle - 1;
    )
  done;
  let col = off - self.lines.(!low) + 1 in
  let line = !low + 1 in
  line, col

let find_line_offset (self:t) ~line : int =
  let line = line-1 in
  if line >= Array.length self.lines then (
    self.size
  ) else (
    Array.get self.lines line
  )

let find_offset (self:t) ~line ~col : int =
  let off = find_line_offset self ~line in
  off + (col - 1)
