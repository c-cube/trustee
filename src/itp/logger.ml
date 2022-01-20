
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
  let lock = Mutex.create() in
  Fmt.set_color_tag_handling fmt;
  { buf; fmt; lock; chans=[]; }

let log_to_chan self oc : unit =
  self.chans <- oc :: self.chans

let as_reporter self : Logs.reporter =
  let output_all () =
    let s = Buffer.contents self.buf in
    List.iter
      (fun oc -> output_string oc s; flush oc) self.chans
  in
  let pp_level_ out = function
    | Logs.Debug -> Fmt.fprintf out "@{<bold>debug@}"
    | Logs.Info -> Fmt.fprintf out "@{<Blue>INFO@}"
    | Logs.App -> Fmt.fprintf out "app"
    | Logs.Error -> Fmt.fprintf out "@{<Red>ERROR@}"
    | Logs.Warning -> Fmt.fprintf out "@{<Yellow>WARN@}"
  in
  { Logs.report =
      fun src lvl ~over k msg ->
        if self.chans <> [] then (
          Mutex.lock self.lock;
          CCFun.protect ~finally:(fun () -> Mutex.unlock self.lock) @@ fun () ->
          Buffer.clear self.buf;
          Fmt.fprintf self.fmt "(@[%a[%s" pp_level_ lvl (Logs.Src.name src);
          msg (fun ?header ?(tags=Logs.Tag.empty) fmt ->
              Option.iter (fun s -> Fmt.fprintf self.fmt ",%s" s) header;
              if not (Logs.Tag.is_empty tags) then Logs.Tag.pp_set self.fmt tags;
              Fmt.fprintf self.fmt "]@ ";
              Fmt.kfprintf
                (fun _ ->
                   Fmt.fprintf self.fmt "@])@.";
                   output_all(); (* output content of [self.buf] *)
                   over();
                   k())
                self.fmt fmt
            )
        ) else k()
  }

let setup_trustee () =
  let open Trustee_core.Log in
  let logger = {
    log=fun lvl k ->
      let k2 f = k (fun fmt -> f ?header:None ?tags:None fmt) in
      match lvl with
      | 0 -> Logs.app k2
      | 1 -> Logs.info k2
      | _ -> Logs.debug k2
  } in
  set_logger logger
