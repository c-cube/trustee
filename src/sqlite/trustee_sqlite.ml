(** Sqlite storage for Trustee *)

module DB = Sqlite3

let ( let@ ) f x = f x

let check_rc_ rc =
  if not (DB.Rc.is_success rc) then (
    let msg = DB.Rc.to_string rc in
    Error.failf (fun k -> k "Sqlite error: %s" msg)
  )

let with_stmt db s f =
  let stmt = DB.prepare db s in
  Fun.protect ~finally:(fun () -> DB.reset stmt |> check_rc_) (fun () -> f stmt)

let init_db_ db =
  DB.exec db
    {|
  CREATE TABLE IF NOT EXISTS trustee_storage (
    key TEXT NOT NULL,
    timestamp REAL NOT NULL,
    data BLOB NOT NULL,
    UNIQUE(key) ON CONFLICT FAIL
  ) STRICT;

  CREATE INDEX IF NOT EXISTS trustee_storage_idx on trustee_storage (key);
  |}
  |> check_rc_

let now_ () = Unix.gettimeofday ()

let storage (file : string) : Storage.t =
  ignore
    (Sys.command (Printf.sprintf "mkdir -p %S" @@ Filename.dirname file) : int);
  let db = DB.db_open ~uri:false ~memory:false ~mutex:`NO file in
  DB.exec db "pragma journal_mode=WAL;" |> check_rc_;
  (* WAL is often faster for insertion *)
  DB.busy_timeout db 3_000;
  init_db_ db;

  let mem_stmt =
    DB.prepare db
      {| SELECT EXISTS (SELECT * FROM trustee_storage WHERE key = ?); |}
  in

  let insert_stmt =
    DB.prepare db
      {|
      INSERT INTO trustee_storage VALUES (?1, ?2, ?3)
      ON CONFLICT(key) DO UPDATE SET timestamp=max(timestamp, ?2);
    |}
  in

  let module M = struct
    let mem ~key : bool =
      (*Format.printf "MEM %S@." key;*)
      let stmt = mem_stmt in
      DB.reset stmt |> check_rc_;
      DB.bind_text stmt 1 key |> check_rc_;
      let rc = DB.step stmt in
      assert (rc = DB.Rc.ROW);
      DB.column_bool stmt 0

    let get ~key dec =
      (*Format.printf "GET %S@." key;*)
      let@ stmt =
        with_stmt db {| SELECT data FROM trustee_storage WHERE key = ?; |}
      in
      DB.bind_text stmt 1 key |> check_rc_;
      let rc = DB.step stmt in
      if rc = DB.Rc.ROW then (
        let data = DB.column_blob stmt 0 in
        Some (Cbor_pack.decode_string_exn dec data)
      ) else (
        check_rc_ rc;
        None
      )

    let store ~key ?(erase = true) enc x =
      (*Format.printf "STORE %S@." key;*)
      let go = erase || not (mem ~key) in
      if go then (
        let stmt = insert_stmt in
        DB.reset stmt |> check_rc_;
        DB.bind_text stmt 1 key |> check_rc_;
        DB.bind_double stmt 2 (now_ ()) |> check_rc_;
        DB.bind_blob stmt 3 (Cbor_pack.encode_to_string enc x) |> check_rc_;
        DB.step stmt |> check_rc_
      )
  end in
  (module M)

let storage_xdg_cache () : Storage.t =
  let dir = Xdg.cache_dir () in
  let file = Filename.concat dir "storage.db" in
  storage file
