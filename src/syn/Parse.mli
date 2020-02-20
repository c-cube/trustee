
open Trustee
module Ctx = Statement.Ctx

val parse_statement : Ctx.t -> string -> (Statement.t, string) result

val parse_statement_exn : Ctx.t -> string -> Statement.t

val parse_statement_l : Ctx.t -> string -> (Statement.t list, string) result

val parse_statement_l_exn : Ctx.t -> string -> Statement.t list
