
type t
val of_string : string -> t
val line_col_of_offset : t -> off:int -> int*int
val find_line_offset : t -> line:int -> int
val find_offset : t -> line:int -> col:int -> int
