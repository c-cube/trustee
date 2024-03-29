(** {1 Positions}

    A position in a string. Line and column are 1-based, so that compatibility
    with LSP is easier. *)

open Common_

type t

val pp : t Fmt.printer

val line : t -> int

val col : t -> int

val none : t

val make : line:int -> col:int -> t

val of_lex : Lexing.position -> t

val ( <= ) : t -> t -> bool

val ( < ) : t -> t -> bool

val ( = ) : t -> t -> bool

val min : t -> t -> t

val max : t -> t -> t
