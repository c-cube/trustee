open Trustee_core

type t = {
  path: string list;
  name: string;
}

let unescape s : string =
  let n = String.length s in
  let buf = Buffer.create (String.length s) in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    match c with
    | '\\' when !i + 1 < n ->
      (match s.[!i + 1] with
      | 'n' ->
        Buffer.add_char buf '\n';
        i := !i + 2
      | '"' ->
        Buffer.add_char buf '"';
        i := !i + 2
      | '\\' ->
        Buffer.add_char buf '\\';
        i := !i + 2
      | _ ->
        Buffer.add_char buf c;
        incr i)
    | _ ->
      Buffer.add_char buf c;
      incr i
  done;
  Buffer.contents buf

let of_string s : t =
  let s = unescape s in
  match CCString.split_on_char '.' s with
  | [ name ] -> { path = []; name }
  | [] -> Error.failf (fun k -> k "invalid name: '%s'" s)
  | l ->
    let name = List.hd @@ CCList.last 1 l in
    let path = CCList.take (List.length l - 1) l in
    { path; name }

let to_string (self : t) =
  match self.path with
  | [] -> self.name
  | ps -> String.concat "." ps ^ "." ^ self.name

let pp out self = Fmt.string out (to_string self)
