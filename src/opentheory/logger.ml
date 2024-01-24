module Fmt = CCFormat

type t = {
  buf: Buffer.t;
  fmt: Format.formatter;
  lock: Mutex.t;
  mutable chans: out_channel list;
}

let create () : t =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  let lock = Mutex.create () in
  Fmt.set_color_tag_handling fmt;
  { buf; fmt; lock; chans = [] }

let log_to_chan self oc : unit = self.chans <- oc :: self.chans

let show_lvl = function
  | Logs.Debug -> "<7>DEBUG"
  | Logs.Info -> "<6>INFO"
  | Logs.Error -> "<3>ERROR"
  | Logs.Warning -> "<4>WARNING"
  | Logs.App -> "<5>APP"

let pp_level_color out = function
  | Logs.Debug -> Fmt.fprintf out "@{<bold>debug@}"
  | Logs.Info -> Fmt.fprintf out "@{<Blue>INFO@}"
  | Logs.App -> Fmt.fprintf out "APP"
  | Logs.Error -> Fmt.fprintf out "@{<Red>ERROR@}"
  | Logs.Warning -> Fmt.fprintf out "@{<Yellow>WARN@}"

let output_all (self : t) =
  let s = Buffer.contents self.buf in
  List.iter
    (fun oc ->
      output_string oc s;
      flush oc)
    self.chans

let as_reporter self : Logs.reporter =
  {
    Logs.report =
      (fun src lvl ~over k msg ->
        if self.chans <> [] then (
          Mutex.lock self.lock;
          CCFun.protect ~finally:(fun () -> Mutex.unlock self.lock) @@ fun () ->
          Buffer.clear self.buf;
          Fmt.fprintf self.fmt "(@[%a[%s" pp_level_color lvl (Logs.Src.name src);
          msg (fun ?header ?(tags = Logs.Tag.empty) fmt ->
              Option.iter (fun s -> Fmt.fprintf self.fmt ",%s" s) header;
              if not (Logs.Tag.is_empty tags) then Logs.Tag.pp_set self.fmt tags;
              Fmt.fprintf self.fmt "]@ ";
              Fmt.kfprintf
                (fun _ ->
                  Fmt.fprintf self.fmt "@])@.";
                  output_all self;
                  (* output content of [self.buf] *)
                  over ();
                  k ())
                self.fmt fmt)
        ) else
          k ());
  }

let as_basic_reporter (self : t) : Logs.reporter =
  {
    Logs.report =
      (fun src lvl ~over k msg ->
        let pp_header out (lvl, src) : unit =
          let src =
            match src with
            | None -> ""
            | Some s -> Printf.sprintf "[%s]" s
          in
          Fmt.fprintf out "%s%s: " (show_lvl lvl) src
        in

        if self.chans <> [] then (
          Mutex.lock self.lock;
          CCFun.protect ~finally:(fun () -> Mutex.unlock self.lock) @@ fun () ->
          Buffer.clear self.buf;
          let src = Logs.Src.name src in
          let src =
            if src = "" then
              None
            else
              Some src
          in
          pp_header self.fmt (lvl, src);
          msg (fun ?header:_ ?tags:_ fmt ->
              Fmt.kfprintf
                (fun _ ->
                  Fmt.fprintf self.fmt "@.";
                  output_all self;
                  (* output content of [self.buf] *)
                  over ();
                  k ())
                self.fmt fmt)
        ) else
          k ());
  }

let setup_trustee_ =
  lazy
    (let open Trustee_core.Log in
    let logger =
      {
        log =
          (fun lvl k ->
            let k2 f = k (fun fmt -> f ?header:None ?tags:None fmt) in
            match lvl with
            | 0 -> Logs.app k2
            | 1 -> Logs.info k2
            | _ -> Logs.debug k2);
      }
    in
    set_logger logger)

let setup_trustee () = Lazy.force setup_trustee_

let setup_logs ?(files = []) ~(style : [ `COLOR | `SYSTEMD ]) ~debug ~level () =
  setup_trustee ();
  let l = create () in
  log_to_chan l stdout;
  let rep =
    match style with
    | `COLOR -> as_reporter l
    | `SYSTEMD ->
      Logs.set_reporter_mutex
        ~lock:(fun () -> Mutex.lock l.lock)
        ~unlock:(fun () -> Mutex.unlock l.lock);
      as_basic_reporter l
  in

  Logs.set_reporter rep;
  Logs.set_level ~all:true
    (Some
       (if debug then
         Logs.Debug
       else
         Logs.Warning));
  Trustee_core.Log.set_level level;
  Logs.app (fun k -> k "logs are set up (debug=%b)" debug);
  List.iter
    (fun file ->
      Logs.info (fun k -> k "logs to file %S" file);
      let oc = open_out_bin file in
      log_to_chan l oc;
      at_exit (fun () -> close_out_noerr oc))
    files;
  ()
