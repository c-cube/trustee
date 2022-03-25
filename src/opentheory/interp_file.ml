open Trustee_core
type 'a or_error = 'a Trustee_core.Error.or_error

type item =
  | I_ty of string * string
  | I_const of string * string

type t = item list

let is_empty = CCList.is_empty
let size self = List.length self
let items_iter self = Iter.of_list self

let pp_item out = function
  | I_ty (s,s2) -> Fmt.fprintf out "type %S as %S" s s2
  | I_const (s,s2) -> Fmt.fprintf out "const %S as %S" s s2

let pp out self =
  Fmt.fprintf out "@[<v>%a@]" (Fmt.list pp_item) self


module P = CCParse

open P

let p_white_ =
  fix @@ fun self ->
  skip_white *>
  ((eoi)
   <|>
   ((char '#') *> P.skip_chars (function '\n' -> false | _ -> true) *> self)
   <|> return ())

let p_quoted : string P.t =
  skip_white *> char '"' *> chars_if (function '"' -> false|_ -> true) <* char '"'

let parse_item : item P.t =
  p_white_ *>
  (((string "type ") *> skip_white *>
    p_quoted >>= fun s ->
    skip_white *> string "as" *> skip_white *>
    p_quoted >|= fun t -> I_ty(s,t))
   <|>
   ((string "const ") *> skip_white *>
    p_quoted >>= fun s ->
    skip_white *> string "as" *> skip_white *>
    p_quoted >|= fun t -> I_const(s,t))
   <?> "expected item") <* p_white_

let parse : _ P.t =
  p_white_ *>
  ((eoi *> return [])
   <|>
   (many parse_item <* eoi))

let item_of_string s =
  match P.parse_string parse_item s with
  | Ok x -> Ok x
  | Error e -> Error (Trustee_core.Error.make e)

let of_string s =
  match P.parse_string parse s with
  | Ok x -> Ok x
  | Error e -> Error (Trustee_core.Error.make e)

