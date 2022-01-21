
type precedence = int

type t =
  | F_normal
  | F_infix of precedence
  | F_left_assoc of precedence
  | F_right_assoc of precedence
  | F_prefix of precedence
  | F_postfix of precedence
  | F_binder of precedence

(* NOTE: must be able to reparse this *)
let pp_syntax out = function
  | F_normal -> Fmt.string out "normal"
  | F_infix i -> Fmt.fprintf out "infix %d" i
  | F_left_assoc i -> Fmt.fprintf out "lassoc %d" i
  | F_right_assoc i -> Fmt.fprintf out "rassoc %d" i
  | F_postfix i -> Fmt.fprintf out "postfix %d" i
  | F_prefix i -> Fmt.fprintf out "prefix %d" i
  | F_binder i -> Fmt.fprintf out "binder %d" i

let to_string_syntax = Fmt.to_string pp_syntax
let pp = pp_syntax
let to_string = Fmt.to_string pp

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
