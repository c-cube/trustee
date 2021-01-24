
open Sigs

type t =
  | F_normal
  | F_infix of int
  | F_left_assoc of int
  | F_right_assoc of int
  | F_prefix of int
  | F_postfix of int
  | F_binder of int

let pp out = function
  | F_normal -> Fmt.string out "normal"
  | F_infix i -> Fmt.fprintf out "infix %d" i
  | F_left_assoc i -> Fmt.fprintf out "lassoc %d" i
  | F_right_assoc i -> Fmt.fprintf out "rassoc %d" i
  | F_postfix i -> Fmt.fprintf out "postfix %d" i
  | F_prefix i -> Fmt.fprintf out "prefix %d" i
  | F_binder i -> Fmt.fprintf out "binder %d" i
let to_string = Fmt.to_string pp

(* NOTE: must be able to reparse this *)
let to_string_syntax = to_string

let normal = F_normal
let prefix i = F_prefix i
let postfix i = F_postfix i
let lassoc i = F_left_assoc i
let rassoc i = F_right_assoc i
let binder i = F_binder i
let infix i = F_infix i

let get_prec = function
  | F_normal -> 1024
  | F_prefix i | F_postfix i | F_left_assoc i | F_infix i
  | F_right_assoc i | F_binder i -> i
