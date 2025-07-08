module LL = Local_loc

type ctx = Local_loc.ctx

type t = {
  loc: Local_loc.t;
  ctx: Local_loc.ctx;
}

let pp_compact out { ctx; loc } = LL.pp ~ctx out loc
let filename self = self.ctx.LL.filename
let local_loc self = self.loc
let same_local_loc a b = LL.equal a.loc b.loc
let make ~ctx loc : t = { loc; ctx }

let none : t =
  let ctx = LL.create ~filename:"<none>" "" in
  make ~ctx LL.none

let create_ctx_string = LL.create
let create_ctx_file = LL.create_file
let of_lex_pos ~ctx p1 p2 : t = make ~ctx (LL.of_lex_pos ~ctx p1 p2)
let of_lexbuf ~ctx (b : Lexing.lexbuf) : t = make ~ctx (LL.of_lexbuf ~ctx b)

let contains { loc; ctx } p =
  let offset = LL.offset_of_pos ~ctx p in
  LL.contains loc ~off:offset

let positions { loc; ctx } = LL.positions ~ctx loc
let union a b : t = { ctx = a.ctx; loc = LL.(a.loc ++ b.loc) }
let union_l a ~f l = List.fold_left (fun l x -> union l (f x)) a l

module Infix = struct
  let ( ++ ) = union
end

include Infix

module Util_pp_loc : sig
  val pp : t Fmt.printer
  val pp_l : t list Fmt.printer
end = struct
  let conv_loc_input (self : Loc_input.t) =
    match Loc_input.view self with
    | Loc_input.String s -> Pp_loc.Input.string s
    | Loc_input.File s -> Pp_loc.Input.file s

  let to_pp_loc (self : t) : Pp_loc.loc =
    let off1, off2 = LL.offsets self.loc in
    ( LL.tr_position ~ctx:self.ctx ~left:true ~offset:off1,
      LL.tr_position ~ctx:self.ctx ~left:false ~offset:off2 )

  let pp out (self : t) : unit =
    if self == none then
      ()
    else (
      let input = conv_loc_input self.ctx.input in
      Format.fprintf out "@[<v>%a@ %a@]" (LL.pp ~ctx:self.ctx) self.loc
        (Pp_loc.pp ~max_lines:5 ~input)
        [ to_pp_loc self ]
    )

  let pp_l out (l : t list) : unit =
    match l with
    | [] -> ()
    | l1 :: _ ->
      let ctx = l1.ctx in
      let input = conv_loc_input ctx.input in
      let locs = List.map to_pp_loc l in
      Format.fprintf out "@[<v>%a@ %a@]"
        Fmt.(list ~sep:(return ";@ and ") pp_compact)
        l
        (Pp_loc.pp ~max_lines:5 ~input)
        locs
end

let pp = Util_pp_loc.pp
let pp_l = Util_pp_loc.pp_l
