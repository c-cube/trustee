module Dec = Decode

let is_stop s i = Char.code (String.unsafe_get s i) lsr 4 = 0

let add_le buf n bytes =
  for i = 0 to bytes - 1 do
    Buffer.add_char buf (Char.unsafe_chr ((n lsr (8 * i)) land 0xff))
  done

let add_uint buf ~high n =
  let byte c = Buffer.add_char buf (Char.unsafe_chr c) in
  if n < 12 then
    byte ((high lsl 4) lor n)
  else if n < 0x100 then (
    byte ((high lsl 4) lor 12);
    byte n
  ) else if n < 0x10000 then (
    byte ((high lsl 4) lor 13);
    add_le buf n 2
  ) else if n < 0x100000000 then (
    byte ((high lsl 4) lor 14);
    add_le buf n 4
  ) else (
    byte ((high lsl 4) lor 15);
    add_le buf n 8
  )

let node_refs data start : int list =
  let dec = Dec.create data in
  Dec.read_node dec start (fun nd _cmd ->
      let acc = ref [] in
      let rec loop () =
        if not (is_stop data nd.off) then (
          match Dec.read nd with
          | Dec.Ref r ->
            acc := r :: !acc;
            loop ()
          | _ -> loop ()
        )
      in
      loop ();
      List.rev !acc)

let node_starts data : int list =
  let dec = Dec.create data in
  let acc = ref [] in
  Dec.iter_nodes dec (fun off _cmd _args -> acc := off :: !acc);
  List.rev !acc

let emit_node ~src ~(map : int -> int) buf start =
  let dec = Dec.create src in
  Dec.read_node dec start (fun nd _cmd ->
      Buffer.add_substring buf src start (nd.off - start);
      let rec loop () =
        if is_stop src nd.off then
          Buffer.add_char buf src.[nd.off]
        else (
          let vstart = nd.off in
          match Dec.read nd with
          | Dec.Ref r ->
            add_uint buf ~high:7 (map r);
            loop ()
          | _ ->
            Buffer.add_substring buf src vstart (nd.off - vstart);
            loop ()
        )
      in
      loop ())

let slice ~data ~root : string * int =
  let seen = Hashtbl.create 64 in
  let stack = Stack.create () in
  Stack.push root stack;
  while not (Stack.is_empty stack) do
    let off = Stack.pop stack in
    if not (Hashtbl.mem seen off) then (
      Hashtbl.add seen off ();
      List.iter
        (fun r -> if not (Hashtbl.mem seen r) then Stack.push r stack)
        (node_refs data off)
    )
  done;
  let starts =
    Hashtbl.fold (fun off () acc -> off :: acc) seen [] |> List.sort compare
  in
  let buf = Buffer.create 1024 in
  let map = Hashtbl.create (List.length starts) in
  let lookup r =
    match Hashtbl.find_opt map r with
    | Some r' -> r'
    | None -> failwith "minidag slice: forward ref"
  in
  List.iter
    (fun old ->
      Hashtbl.add map old (Buffer.length buf);
      emit_node ~src:data ~map:lookup buf old)
    starts;
  Buffer.contents buf, lookup root

let merge (slices : (string * int) list) : string * int list =
  let buf = Buffer.create 1024 in
  let roots =
    List.map
      (fun (data, root) ->
        (* Re-encoding a shifted ref can change its width, so offsets in the
           output are not [base + offset]; track them while emitting. *)
        let map = Hashtbl.create 64 in
        let lookup r =
          match Hashtbl.find_opt map r with
          | Some r' -> r'
          | None -> failwith "minidag merge: forward ref"
        in
        List.iter
          (fun start ->
            Hashtbl.add map start (Buffer.length buf);
            emit_node ~src:data ~map:lookup buf start)
          (node_starts data);
        lookup root)
      slices
  in
  Buffer.contents buf, roots
