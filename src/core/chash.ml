open Sigs
module H = Sha256

type t = bytes (* binary content *)

type ctx = {
  buf: bytes; (* len=8 *)
  ctx: H.ctx;
}

let unsafe_to_bytes (self : t) =
  assert (Bytes.length self = 32);
  Bytes.copy self

let unsafe_of_string s : t =
  assert (String.length s = 32);
  Bytes.unsafe_of_string s

let unsafe_of_bytes b : t =
  assert (Bytes.length b = 32);
  Bytes.copy b

let dummy = Bytes.unsafe_of_string "<dummy>"
let create () = { ctx = H.init (); buf = Bytes.create 8 }
let equal = Bytes.equal
let hash = CCHash.bytes
let compare = Bytes.compare
let[@inline] string ctx s = H.update_string ctx.ctx s

let[@inline] int ctx i =
  Bytes.set_int64_le ctx.buf 0 (Int64.of_int i);
  H.update_substring ctx.ctx (Bytes.unsafe_to_string ctx.buf) 0 8

let[@inline] sub ctx (self : t) =
  H.update_substring ctx.ctx (Bytes.unsafe_to_string self) 0 (Bytes.length self)

let[@inline] finalize ctx : t =
  let s = H.to_bin (H.finalize ctx.ctx) in
  Bytes.unsafe_of_string s

type 'a hasher = ctx -> 'a -> unit

let run hasher x =
  let ctx = create () in
  hasher ctx x;
  finalize ctx

let str_to_hex (s : string) =
  let i_to_hex (i : int) =
    if i < 10 then
      Char.chr (i + Char.code '0')
    else
      Char.chr (i - 10 + Char.code 'a')
  in

  let res = Bytes.create (2 * String.length s) in
  for i = 0 to String.length s - 1 do
    let n = Char.code (String.get s i) in
    Bytes.set res (2 * i) (i_to_hex ((n land 0xf0) lsr 4));
    Bytes.set res ((2 * i) + 1) (i_to_hex (n land 0x0f))
  done;
  Bytes.unsafe_to_string res

(* hex representation *)
let to_string (self : t) : string =
  let s = Bytes.unsafe_to_string self in
  str_to_hex s

let pp out self = Fmt.string out (to_string self)

let of_hex_exn (s : string) : string =
  let n_of_c = function
    | '0' .. '9' as c -> Char.code c - Char.code '0'
    | 'a' .. 'f' as c -> 10 + Char.code c - Char.code 'a'
    | _ -> invalid_arg "string: invalid hex"
  in
  if String.length s mod 2 <> 0 then
    invalid_arg "string: hex sequence must be of even length";
  let res = Bytes.make (String.length s / 2) '\x00' in
  for i = 0 to (String.length s / 2) - 1 do
    let n1 = n_of_c (String.get s (2 * i)) in
    let n2 = n_of_c (String.get s ((2 * i) + 1)) in
    let n = (n1 lsl 4) lor n2 in
    Bytes.set res i (Char.chr n)
  done;
  Bytes.unsafe_to_string res

let of_string_exn s : t = of_hex_exn s |> Bytes.unsafe_of_string

let enc enc (self : t) =
  Cbor_pack.Enc.(add_entry enc @@ blob (Bytes.unsafe_to_string self))

let dec =
  Cbor_pack.Dec.(
    let+ b = blob in
    unsafe_of_string b)

module As_key = struct
  type nonrec t = t

  let equal = equal
  let hash = hash
end

module Tbl = CCHashtbl.Make (As_key)
