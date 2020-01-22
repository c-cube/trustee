
module Ctx = Statement.Ctx

val parse_statement : Ctx.t -> string -> (Statement.t, string) result

val parse_statement_exn : Ctx.t -> string -> Statement.t
