
type item =
  | I_ty of string * string
  | I_const of string * string

type t = {
  items: item list;
}

let size self = List.length self.items

let pp_item out = function
  | I_ty (s,s2) -> Fmt.fprintf out "type %S as %S" s s2
  | I_const (s,s2) -> Fmt.fprintf out "const %S as %S" s s2

let pp out self =
  Fmt.fprintf out "@[<v>%a@]" (Fmt.list pp_item) self.items


module P = CCParse

open P

let p_white_ =
  fix @@ fun self ->
  skip_white *>
  ((try_ eoi)
   <|>
   (try_ (char '#') *> P.skip_chars (function '\n' -> false | _ -> true) *> self)
   <|> return ())

let p_quoted : string P.t =
  skip_white *> char '"' *> chars_if (function '"' -> false|_ -> true) <* char '"'

let parse_item : item P.t =
  p_white_ *>
  ((try_ (string "type ") *> skip_white *>
    p_quoted >>= fun s ->
    skip_white *> string "as" *> skip_white *>
    p_quoted >|= fun t -> I_ty(s,t))
   <|>
   (try_ (string "const ") *> skip_white *>
    p_quoted >>= fun s ->
    skip_white *> string "as" *> skip_white *>
    p_quoted >|= fun t -> I_const(s,t))
   <?> "expected item") <* p_white_

let parse : _ P.t =
  p_white_ *>
  ((try_ eoi *> return [])
   <|>
   (many parse_item <* eoi))
  >|= fun items -> {items}

let of_string s =
  match P.parse_string parse s with
  | Ok x -> Ok x
  | Error e -> Error (Trustee_error.mk e)

