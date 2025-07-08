open Sigs
module K = Kernel
module E = K.Expr

type rw_step =
  | Same
  | Rw_step of K.thm

type t = K.ctx -> K.expr -> rw_step

let pp_rw_step out = function
  | Same -> Fmt.string out "same"
  | Rw_step th -> Fmt.fprintf out "(@[rw-step@ `%a`@])" K.Thm.pp th

let thm_res_eqn thm : E.t * E.t =
  match E.unfold_eq (K.Thm.concl thm) with
  | None ->
    Error.failf (fun k -> k "rw: theorem %a should be an equation" K.Thm.pp thm)
  | Some pair -> pair

let[@inline] thm_res_rhs th : E.t = snd (thm_res_eqn th)
let empty : t = fun _ctx _e -> Same

let apply (self : t) ctx e =
  match self ctx e with
  | Same -> K.Thm.refl ctx e
  | Rw_step th -> th

let apply_e self ctx e =
  let th = apply self ctx e in
  thm_res_rhs th, th

let[@inline] chain_res ctx r1 r2 =
  match r1, r2 with
  | Same, r2 -> r2
  | r1, Same -> r1
  | Rw_step th1, Rw_step th2 -> Rw_step (K.Thm.trans ctx th1 th2)

let fix self : t =
 fun ctx e ->
  (* rewrite in a loop until the conversion doesn't apply anymore *)
  let rec loop_ step1 e =
    match self ctx e with
    | Same -> step1
    | Rw_step th2 as step2 ->
      let step, e' =
        match step1 with
        | Same -> step2, thm_res_rhs th2
        | Rw_step th1 ->
          (* compose steps *)
          let th = K.Thm.trans ctx th1 th2 in
          Rw_step th, thm_res_rhs th
      in
      (loop_ [@tailcall]) step e'
  in
  loop_ Same e

let combine a b : t =
  if a == empty then
    b
  else if b == empty then
    a
  else
    fun ctx e ->
  match a ctx e with
  | Same -> b ctx e
  | Rw_step _ as r -> r

let combine_l = function
  | [] -> empty
  | [ c ] -> c
  | [ c1; c2 ] -> combine c1 c2
  | l ->
    fun ctx e ->
      let rec loop_ = function
        | [] -> Same
        | c1 :: tl ->
          (match c1 ctx e with
          | Rw_step _ as r -> r
          | Same -> loop_ tl)
      in
      loop_ l
