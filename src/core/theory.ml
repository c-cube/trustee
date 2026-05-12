open Types
open Sigs
module H = CCHash
module Const_def = Const.Const_def

type t = theory

let name self = self.theory_name

let param_consts self =
  Name_k_map.values self.theory_in_constants |> Iter.to_list

let param_theorems self = self.theory_in_theorems

let consts self =
  Name_k_map.values self.theory_defined_constants |> Iter.to_list

let theorems self = self.theory_defined_theorems
let pp_name out self = Fmt.string out self.theory_name

let pp out (self : t) : unit =
  let {
    theory_name = name;
    theory_ctx = _;
    theory_in_constants = inc;
    theory_in_theorems = inth;
    theory_defined_theorems = dth;
    theory_defined_constants = dc;
  } =
    self
  in
  Fmt.fprintf out "(@[<v1>theory %a" Fmt.string name;
  Name_k_map.iter
    (fun _ c -> Fmt.fprintf out "@,(@[in-const@ %a@])" Const.pp_with_ty c)
    inc;
  List.iter
    (fun th -> Fmt.fprintf out "@,(@[in-thm@ %a@])" Thm.pp_quoted th)
    inth;
  Name_k_map.iter
    (fun _ c ->
      Fmt.fprintf out "@,(@[defined-const@ %a@])" Const.pp_with_ty c)
    dc;
  List.iter
    (fun th -> Fmt.fprintf out "@,(@[defined-thm@ %a@])" Thm.pp_quoted th)
    dth;
  Fmt.fprintf out "@])";
  ()

let to_string = Fmt.to_string pp

let assume self hyps concl : thm =
  let ctx = self.theory_ctx in
  Error.guard (fun err ->
      Error.wrapf "in theory_assume@ `@[%a@ |- %a@]`:" (pp_list Expr.pp) hyps
        Expr.pp concl err)
  @@ fun () ->
  if not (Thm.is_bool_ ctx concl && List.for_all (Thm.is_bool_ ctx) hyps) then
    Error.fail "Theory.assume: all terms must be booleans";
  let hyps = Expr_set.of_list hyps in
  let proof () = Proof.(step "th.assume") in
  let th = Thm.make_ ctx hyps concl proof (Some self) in
  self.theory_in_theorems <- th :: self.theory_in_theorems;
  th

let add_assumption_const self (c : const) : unit =
  let kind =
    if Expr.is_eq_to_type c.c_ty then
      C_ty
    else
      C_term
  in
  if Name_k_map.mem (kind, c.c_name) self.theory_in_constants then
    Error.failf (fun k ->
        k "Theory.assume_const: constant `%a` already exists" Fmt.string
          c.c_name);
  self.theory_in_constants <-
    Name_k_map.add (kind, c.c_name) c self.theory_in_constants;
  ()

let assume_const self name ty_vars ty : const =
  let c =
    Const.new_const
      ~def:(C_def_theory_param { ty_vars; ty })
      self.theory_ctx name ty_vars ty
  in
  add_assumption_const self c;
  c

let assume_ty_const self name ~arity : const =
  let c =
    Const.new_ty_const self.theory_ctx name arity
      ~def:(C_def_theory_ty_param { arity })
  in
  add_assumption_const self c;
  c

let add_const_ self c : unit =
  let key = c.c_name in
  let kind =
    if Expr.is_eq_to_type c.c_ty then
      C_ty
    else
      C_term
  in
  (match Name_k_map.get (kind, key) self.theory_defined_constants with
  | Some c' when Const.equal c c' ->
    Log.debugf 2 (fun k -> k "redef `%a`" Fmt.string key)
  | Some _ ->
    Error.failf (fun k ->
        k "Theory.add_const: constant `%a` already defined" Fmt.string key)
  | None -> ());
  self.theory_defined_constants <-
    Name_k_map.add (kind, key) c self.theory_defined_constants

let add_const = add_const_
let add_ty_const = add_const_

let[@inline] find_const self s : _ option =
  try Some (Name_k_map.find (C_term, s) self.theory_defined_constants)
  with Not_found -> Name_k_map.get (C_term, s) self.theory_in_constants

let[@inline] find_ty_const self s : _ option =
  try Some (Name_k_map.find (C_ty, s) self.theory_defined_constants)
  with Not_found -> Name_k_map.get (C_ty, s) self.theory_in_constants

let add_theorem self th : unit =
  (match th.th_theory with
  | None -> th.th_theory <- Some self
  | Some th' when self != th' ->
    Error.failf (fun k -> k "add theorem %a@ from the wrong theory" Thm.pp th)
  | Some _ -> ());
  self.theory_defined_theorems <- th :: self.theory_defined_theorems

let mk_ ctx ~name : t =
  {
    theory_name = name;
    theory_ctx = ctx;
    theory_in_constants = Name_k_map.empty;
    theory_defined_constants = Name_k_map.empty;
    theory_in_theorems = [];
    theory_defined_theorems = [];
  }

let mk_str_ ctx ~name : t = mk_ ctx ~name

let with_ ctx ~name f : t =
  let self = mk_str_ ctx ~name in
  f self;
  self

let check_same_ctx_ ctx l =
  List.iter
    (fun th ->
      if th.theory_ctx != ctx then
        Error.failf (fun k ->
            k "theory `%a` comes from a different context" pp_name th))
    l

let union_const_map_ ctx ~what m1 m2 =
  Name_k_map.union
    (fun (_, n) c1 c2 ->
      if not (Const.equal c1 c2) then (
        let d1 = Const.get_def_exn ctx c1 in
        let d2 = Const.get_def_exn ctx c2 in
        Error.failf (fun k ->
            k "incompatible %s constant `%a`: %a vs %a@ :def1 %a@ :def2 %a"
              what Fmt.string n Const.pp_cname c1 Const.pp_cname c2
              Const_def.pp d1 Const_def.pp d2)
      );
      Some c1)
    m1 m2

let union ctx ~name l : t =
  check_same_ctx_ ctx l;
  let self = mk_str_ ctx ~name in
  let in_th =
    Iter.of_list self.theory_in_theorems
    |> Iter.map (fun th -> th, ())
    |> Thm.Tbl.of_iter_with ~f:(fun _ () () -> ())
  and out_th =
    Iter.of_list self.theory_defined_theorems
    |> Iter.map (fun th -> th, ())
    |> Thm.Tbl.of_iter_with ~f:(fun _ () () -> ())
  in
  List.iter
    (fun th ->
      self.theory_in_constants <-
        union_const_map_ ctx ~what:"assumed" self.theory_in_constants
          th.theory_in_constants;
      self.theory_defined_constants <-
        union_const_map_ ctx ~what:"defined" self.theory_defined_constants
          th.theory_defined_constants;
      List.iter (fun th -> Thm.Tbl.replace in_th th ()) th.theory_in_theorems;
      List.iter
        (fun th -> Thm.Tbl.replace out_th th ())
        th.theory_defined_theorems)
    l;
  self.theory_in_theorems <-
    in_th |> Thm.Tbl.to_iter |> Iter.map fst |> Iter.to_rev_list;
  self.theory_defined_theorems <-
    out_th |> Thm.Tbl.to_iter |> Iter.map fst |> Iter.to_rev_list;
  self

type interpretation = string Str_map.t

let pp_interp out (i : interpretation) : unit =
  let pp_pair out (n, u) = Fmt.fprintf out "(@[`%s` =>@ `%s`@])" n u in
  Fmt.fprintf out "{@[%a@]}"
    (Fmt.iter ~sep:(Fmt.return "@ ") pp_pair)
    (Str_map.to_iter i)

module Instantiate_ = struct
  type state = {
    ctx: Ctx.t;
    cache: expr Expr.Tbl.t;
    interp: interpretation;
    find_const: string -> ty:Expr.t -> const option;
  }

  let create ?(find_const = fun _ ~ty:_ -> None) ?(interp = Str_map.empty) ctx
      : state =
    { ctx; interp; cache = Expr.Tbl.create 32; find_const }

  let rec inst_t_ (self : state) (e : expr) : expr =
    let rec loop e =
      match Expr.Tbl.find self.cache e with
      | u -> u
      | exception Not_found ->
        let u =
          match Expr.view e with
          | E_var v -> Expr.var self.ctx (Var.map_ty v ~f:loop)
          | E_const (c, args) ->
            let args' = List.map loop args in
            let c' = inst_const_ self c in
            if c == c' && List.for_all2 Expr.equal args args' then
              e
            else
              Expr.const self.ctx c' args'
          | _ -> Expr.map self.ctx e ~f:(fun _ e' -> loop e')
        in
        Expr.Tbl.add self.cache e u;
        u
    in
    loop e

  and inst_const_ (self : state) (c : const) : const =
    let ty' = inst_t_ self c.c_ty in
    let name' =
      try Str_map.find c.c_name self.interp
      with Not_found -> c.c_name
    in
    match self.find_const name' ~ty:ty' with
    | Some c' when Expr.is_eq_to_type c'.c_ty -> c'
    | Some c' ->
      let c'_def = Const.get_def_exn self.ctx c' in
      let ty'' = inst_t_ self c'.c_ty in
      let def = Const_def.map c'_def ~f:(inst_t_ self) in
      Const.make self.ctx ~def c'.c_name c'.c_args ty''
    | None ->
      (* If nothing changed (no renaming, type unchanged), return the original
         const to preserve physical identity and avoid creating a new record
         with a different c_ty but the same name. *)
      if String.equal name' c.c_name && ty' == c.c_ty then
        c
      else (
        let c_def = Const.get_def_exn self.ctx c in
        let def = Const_def.map c_def ~f:(inst_t_ self) in
        Const.make self.ctx ~def name' c.c_args ty'
      )

  let inst_constants_ (self : state) (m : const Name_k_map.t) : _ Name_k_map.t
      =
    Name_k_map.to_iter m
    |> Iter.map (fun ((k, _), c) ->
           let c' = inst_const_ self c in
           (k, c'.c_name), c')
    |> Name_k_map.of_iter

  let inst_thm_ (self : state) theory (th : thm) : thm =
    let hyps =
      Expr_set.to_iter th.th_seq.hyps
      |> Iter.map (inst_t_ self)
      |> Expr_set.of_iter
    in
    let concl = inst_t_ self th.th_seq.concl in
    let proof () = th.th_proof in
    Thm.make_ self.ctx hyps concl proof (Some theory)

  let inst_theory_ (self : state) (th : theory) : theory =
    assert (self.ctx == th.theory_ctx);
    let {
      theory_ctx = _;
      theory_name;
      theory_in_constants;
      theory_in_theorems;
      theory_defined_constants;
      theory_defined_theorems;
    } =
      th
    in
    let th' = mk_ self.ctx ~name:theory_name in
    th'.theory_in_constants <- inst_constants_ self theory_in_constants;
    th'.theory_defined_constants <-
      inst_constants_ self theory_defined_constants;
    th'.theory_in_theorems <- List.map (inst_thm_ self th') theory_in_theorems;
    th'.theory_defined_theorems <-
      List.map (inst_thm_ self th') theory_defined_theorems;
    th'
end

let instantiate ~(interp : interpretation) th : t =
  if Str_map.is_empty interp then
    th
  else (
    let st = Instantiate_.create ~interp th.theory_ctx in
    Instantiate_.inst_theory_ st th
  )

module Str_ty_tbl = CCHashtbl.Make (struct
  type t = string * Expr.t

  let equal (n1, ty1) (n2, ty2) = String.equal n1 n2 && Expr.equal ty1 ty2
  let hash (n, ty) = H.(combine3 25 (H.string n) (Expr.hash ty))
end)

let compose ?(interp = Str_map.empty) l th : t =
  Log.debugf 2 (fun k ->
      k "(@[theory.compose@ %a@ %a@ @[:interp %a@]@])"
        Fmt.(Dump.list pp_name)
        l pp_name th pp_interp interp);

  if CCList.is_empty l then
    instantiate ~interp th
  else (
    let ctx = th.theory_ctx in

    let const_tbl_ = Str_ty_tbl.create 32 in
    let provided_thms = Thm.Tbl.create 32 in

    List.iter
      (fun th0 ->
        Name_k_map.iter
          (fun _ c -> Str_ty_tbl.replace const_tbl_ (c.c_name, c.c_ty) c)
          th0.theory_in_constants;
        Name_k_map.iter
          (fun _ c -> Str_ty_tbl.replace const_tbl_ (c.c_name, c.c_ty) c)
          th0.theory_defined_constants;
        List.iter
          (fun th -> Thm.Tbl.replace provided_thms th ())
          th0.theory_defined_theorems)
      l;

    let find_const name ~ty = Str_ty_tbl.get const_tbl_ (name, ty) in

    let st = Instantiate_.create ~find_const ~interp ctx in
    let th = Instantiate_.inst_theory_ st th in

    th.theory_in_constants <-
      Name_k_map.filter
        (fun _ c -> not (Str_ty_tbl.mem const_tbl_ (c.c_name, c.c_ty)))
        th.theory_in_constants;
    let in_thm =
      th.theory_in_theorems |> Iter.of_list
      |> Iter.filter (fun thm -> not (Thm.Tbl.mem provided_thms thm))
      |> Iter.map (fun thm -> thm, ())
      |> Thm.Tbl.of_iter
    in
    List.iter
      (fun th' ->
        List.iter
          (fun thm -> Thm.Tbl.replace in_thm thm ())
          th'.theory_in_theorems)
      l;
    th.theory_in_theorems <-
      Thm.Tbl.to_iter in_thm |> Iter.map fst |> Iter.to_rev_list;

    th
  )
