open Sigs

type position = Position.t
type t = {
  start: position;
  stop: position;
  file: string option;
}
let none = {start=Position.none; stop=Position.none; file=None}

let pp out (self:t) : unit =
  let open Position in
  let pp_file out = function
    | None -> ()
    | Some f -> Fmt.fprintf out "@ in '%s'" f
  in
  if self.start.line = self.stop.line then (
    Fmt.fprintf out "%d:%d-%d%a" self.start.line self.start.col self.stop.col
      pp_file self.file
  ) else (
    Fmt.fprintf out "%d:%d-%d:%d%a" self.start.line self.start.col
      self.stop.line self.stop.col
      pp_file self.file
  )
