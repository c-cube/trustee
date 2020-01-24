
exception Error of string

val error : string -> 'a

val errorf : ('a, Format.formatter, unit, 'b) format4 -> 'a

