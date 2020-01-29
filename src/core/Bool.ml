open Trustee_kot

module T = Expr

let and_const : T.t = T.new_const_infix "/\\" T.(bool @-> bool @-> bool)
let or_const : T.t = T.new_const_infix "\\/" T.(bool @-> bool @-> bool)
let not_const : T.t = T.new_const "~" T.(bool @-> bool)

let and_ a b : T.t = T.app_l and_const [a;b]
let or_ a b : T.t = T.app_l or_const [a;b]
let not_ a : T.t = T.app not_const a
let rec and_l = function [] -> T.true_ | [t] -> t | t :: ts -> and_ t (and_l ts)
let rec or_l = function [] -> T.false_ | [t] -> t | t :: ts -> or_ t (or_l ts)

(* TODO: basic theorems for manipulating formulas *)
(* TODO: quantifiers *)
(* TODO: rules to manipulate booleans *)
