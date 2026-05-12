(* vendored from ~/w/granite/src/minidag — keep in sync *)
type t = { str: string }
(** Decoder *)

let create str : t = { str }

type offset = int

type node_decoder = {
  dec: t;
  mutable off: offset;
}

type value =
  | Stop  (** No other value left *)
  | Null
  | Bool of bool
  | Int64 of int64
  | Float of float
  | String of string
  | Blob of string
  | Ref of int

exception Fail of string * offset

let fail off msg = raise (Fail (msg, off))
let failf off msg = Printf.ksprintf (fail off) msg

let[@inline] read_byte_ (self : node_decoder) : int =
  let c = String.get self.dec.str self.off in
  self.off <- self.off + 1;
  Char.code c

let[@inline] read_leading_ (self : node_decoder) =
  let c = read_byte_ self in
  c lsr 4, c land 0x0f

let read_uint64 self ~low =
  match low with
  | _ when low < 12 -> Int64.of_int low
  | 12 -> read_byte_ self |> Int64.of_int
  | 13 ->
    let n = String.get_int16_le self.dec.str self.off in
    self.off <- self.off + 2;
    Int64.of_int (n land 0xFFFF)
    (* strip sign extension: treat as uint16 *)
  | 14 ->
    let n = String.get_int32_le self.dec.str self.off in
    self.off <- self.off + 4;
    Int64.logand (Int64.of_int32 n) 0xFFFFFFFFL (* treat as uint32 *)
  | 15 ->
    let n = String.get_int64_le self.dec.str self.off in
    self.off <- self.off + 8;
    n
  | _ -> assert false

let string_ self ~low : string =
  let len = read_uint64 self ~low |> Int64.to_int in
  let s = String.sub self.dec.str self.off len in
  self.off <- self.off + len;
  s

let read (self : node_decoder) : value =
  let off_start = self.off in
  let high, low = read_leading_ self in
  match high with
  | 0 ->
    (* make sure we can't read further *)
    self.off <- String.length self.dec.str;
    Stop
  | 1 ->
    (match low with
    | 0 -> Null
    | 1 -> Bool true
    | 2 -> Bool false
    | n -> failf off_start "invalid special: %d" n)
  | 2 -> Int64 (read_uint64 self ~low)
  | 3 -> Int64 (Int64.neg (read_uint64 self ~low))
  | 4 -> Float (Int64.float_of_bits (read_uint64 self ~low))
  | 5 -> String (string_ self ~low)
  | 6 -> Blob (string_ self ~low)
  | 7 -> Ref (read_uint64 self ~low |> Int64.to_int)
  | _ -> failf off_start "invalid high: %d" high

let read_node (self : t) (off : offset) f =
  let dec = { dec = self; off } in
  match read dec with
  | String s -> f dec s
  | _ -> fail off "expected node to start with a string"

let iter_nodes (self : t) (f : offset -> string -> value list -> unit) : unit =
  let total_len = String.length self.str in
  let rec go off =
    if off < total_len then (
      let dec = { dec = self; off } in
      match read dec with
      | String cmd ->
        (* save the offset just before each read; when we see Stop, that saved
           value is the Stop byte's position — next node starts one byte later *)
        let stop_off = ref dec.off in
        let rec collect acc =
          stop_off := dec.off;
          match read dec with
          | Stop -> List.rev acc
          | v -> collect (v :: acc)
        in
        let args = collect [] in
        f off cmd args;
        go (!stop_off + 1)
      | _ -> fail off "expected string at start of node"
    )
  in
  go 0

(** Read all values until Stop, returning them as a list. *)
let read_all (nd : node_decoder) : value list =
  let rec loop acc =
    match read nd with
    | Stop -> List.rev acc
    | v -> loop (v :: acc)
  in
  loop []

(** Read all Ref values until Stop, returning offsets as an array.
    Fails if a non-Ref, non-Stop value is encountered. *)
let read_refs (nd : node_decoder) : int array =
  let buf = Buffer.create 8 in
  let rec loop () =
    let off = nd.off in
    match read nd with
    | Stop -> ()
    | Ref r ->
      (* store as 4-byte LE int in buffer *)
      Buffer.add_char buf (Char.chr (r land 0xFF));
      Buffer.add_char buf (Char.chr ((r lsr 8) land 0xFF));
      Buffer.add_char buf (Char.chr ((r lsr 16) land 0xFF));
      Buffer.add_char buf (Char.chr ((r lsr 24) land 0xFF));
      loop ()
    | _ -> fail off "read_refs: expected Ref or Stop"
  in
  loop ();
  let s = Buffer.contents buf in
  let n = String.length s / 4 in
  Array.init n (fun i ->
    let b0 = Char.code s.[i*4] in
    let b1 = Char.code s.[i*4+1] in
    let b2 = Char.code s.[i*4+2] in
    let b3 = Char.code s.[i*4+3] in
    b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24))

(** Read exactly [n] Ref values; fail if not enough or too many. *)
let read_n_refs (nd : node_decoder) (n : int) : int array =
  Array.init n (fun _i ->
    let off = nd.off in
    match read nd with
    | Ref r -> r
    | _ -> fail off (Printf.sprintf "read_n_refs: expected Ref"))

(** Read the next value and assert it is a String; return the string. *)
let read_string_exn (nd : node_decoder) : string =
  let off = nd.off in
  match read nd with
  | String s -> s
  | _ -> fail off "expected String"

(** Read the next value and assert it is an Int64; return it. *)
let read_int64_exn (nd : node_decoder) : int64 =
  let off = nd.off in
  match read nd with
  | Int64 i -> i
  | _ -> fail off "expected Int64"

(** Read the next value and assert it is a Ref; return the offset. *)
let read_ref_exn (nd : node_decoder) : int =
  let off = nd.off in
  match read nd with
  | Ref r -> r
  | _ -> fail off "expected Ref"

(** Read the next value and assert it is a Bool; return it. *)
let read_bool_exn (nd : node_decoder) : bool =
  let off = nd.off in
  match read nd with
  | Bool b -> b
  | _ -> fail off "expected Bool"
