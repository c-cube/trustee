
open Sigs

module K = Kernel
module P = Parser_comb

module Ast = Parse_ast

val ty : Ast.ty P.t
val expr : K.Ctx.t -> Ast.t P.t

val ty_eof : Ast.ty P.t
val expr_eof : K.Ctx.t -> Ast.t P.t
