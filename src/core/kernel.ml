
(** {1 Kernel of trust} *)

open Sigs
module H = CCHash

let ctx_id_bits = 5
let ctx_id_mask = (1 lsl ctx_id_bits) - 1

type location = Loc.t

module Name : sig
  type t = private string
  val make : string -> t
  val equal_str : t -> string -> bool
  include Sigs.EQ with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.HASH with type t := t
  include Sigs.PP with type t := t
end = struct
  type t = string
  let equal = String.equal
  let equal_str = equal
  let compare = String.compare
  let hash = H.string
  let pp = Fmt.string
  let make s = s
  let to_string s = s
end


type expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of string * expr * expr
  | E_arrow of expr * expr

and expr = {
  e_view: expr_view;
  e_ty: expr option lazy_t;
  mutable e_id: int;
  mutable e_flags: int; (* ̵contains: [higher DB var | 1:has free vars | 5:ctx uid] *)
}

and var = {
  v_name: string;
  v_ty: ty;
}
and ty_var = var

and bvar = {
  bv_idx: int;
  bv_ty: ty;
}

and ty = expr

and name = Name.t

and const = {
  c_name: name;
  c_args: const_args;
  c_ty: ty; (* free vars = c_ty_vars *)
  c_def_id: const_def_id;
  c_def_loc: location option;
}
and ty_const = const

and const_def_id =
  | C_def_gen of int (* generative *)
  | C_in_theory of name (* theory name *)

and const_args =
  | C_ty_vars of ty_var list
  | C_arity of int (* for type constants *)

let[@inline] expr_eq (e1:expr) e2 : bool = e1 == e2
let[@inline] expr_hash (e:expr) = H.int e.e_id
let[@inline] expr_compare (e1:expr) e2 : int = CCInt.compare e1.e_id e2.e_id
let[@inline] expr_db_depth e = e.e_flags lsr (1+ctx_id_bits)
let[@inline] expr_has_fvars e = ((e.e_flags lsr ctx_id_bits) land 1) == 1
let[@inline] expr_ctx_uid e : int = e.e_flags land ctx_id_mask

let[@inline] var_eq v1 v2 = v1.v_name = v2.v_name && expr_eq v1.v_ty v2.v_ty
let[@inline] var_hash v1 = H.combine3 5 (H.string v1.v_name) (expr_hash v1.v_ty)
let[@inline] var_pp out v1 = Fmt.string out v1.v_name

let const_def_eq a b =
  match a, b with
  | C_def_gen i, C_def_gen j -> i=j
  | C_in_theory n1, C_in_theory n2 -> Name.equal n1 n2
  | (C_def_gen _ | C_in_theory _), _ -> false

let[@inline] const_eq (c1:const) c2 : bool =
  Name.equal c1.c_name c2.c_name &&
  const_def_eq c1.c_def_id c2.c_def_id

let const_hash c =
  let h_def =
    match c.c_def_id with
    | C_def_gen id -> H.(combine2 12 (int id))
    | C_in_theory n -> H.(combine2 25 (Name.hash n))
  in
  H.combine3 129 (Name.hash c.c_name) h_def

module Const_hashcons = Hashcons.Make(struct
    type t = const
    let equal = const_eq
    let hash = const_hash
    let set_id _ _ = ()
    let on_new _ = ()
  end)

module Expr_set = CCSet.Make(struct
    type t = expr
    let compare = expr_compare
    end)

(* open an application *)
let unfold_app (e:expr) : expr * expr list =
  let rec aux acc e =
    match e.e_view with
    | E_app (f, a) -> aux (a::acc) f
    | _ -> e, acc
  in
  aux [] e

let __pp_ids = ref false

(* debug printer *)
let expr_pp_ out (e:expr) : unit =
  let rec loop k names out e =
    let pp = loop k names in
    let pp' = loop' k names in
    (match e.e_view with
    | E_kind -> Fmt.string out "kind"
    | E_type -> Fmt.string out "type"
    | E_var v -> Fmt.string out v.v_name
    (* | E_var v -> Fmt.fprintf out "(@[%s : %a@])" v.v_name pp v.v_ty *)
    | E_bound_var v ->
      let idx = v.bv_idx in
      begin match CCList.nth_opt names idx with
        | Some n when n<>"" -> Fmt.string out n
        | _ ->
          if idx<k then Fmt.fprintf out "x_%d" (k-idx-1)
          else Fmt.fprintf out "%%db_%d" (idx-k)
      end
    | E_const (c,[]) -> Name.pp out c.c_name
    | E_const (c,args) ->
      Fmt.fprintf out "(@[%a@ %a@])" Name.pp c.c_name (pp_list pp') args
    | E_app _ ->
      let f, args = unfold_app e in
      begin match f.e_view, args with
        | E_const (c, [_]), [a;b] when Name.equal_str c.c_name "=" ->
          Fmt.fprintf out "@[%a@ = %a@]" pp' a pp' b
        | _ ->
          Fmt.fprintf out "@[%a@ %a@]" pp' f (pp_list pp') args
      end
    | E_lam ("", _ty, bod) ->
      Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp' _ty
        (loop (k+1) (""::names)) bod
    | E_lam (n, _ty, bod) ->
      Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" n pp' _ty (loop (k+1) (n::names)) bod
    | E_arrow(a,b) ->
      Fmt.fprintf out "@[%a@ -> %a@]" pp' a pp b
    );
    if !__pp_ids then Fmt.fprintf out "/%d" e.e_id;

  and loop' k names out e = match e.e_view with
    | E_kind | E_type | E_var _ | E_bound_var _ | E_const (_, []) ->
      loop k names out e (* atomic expr *)
    | _ -> Fmt.fprintf out "(%a)" (loop k names) e
  in
  loop 0 [] out e

module Expr_hashcons = Hashcons.Make(struct
    type t = expr

    let equal a b =
      begin match a.e_view, b.e_view with
        | E_kind, E_kind
        | E_type, E_type -> true
        | E_const (c1,l1), E_const (c2,l2) ->
          Name.equal c1.c_name c2.c_name && CCList.equal expr_eq l1 l2
        | E_var v1, E_var v2 -> var_eq v1 v2
        | E_bound_var v1, E_bound_var v2 ->
          v1.bv_idx = v2.bv_idx && expr_eq v1.bv_ty v2.bv_ty
        | E_app (f1,a1), E_app (f2,a2) ->
          expr_eq f1 f2 && expr_eq a1 a2
        | E_lam (_,ty1,bod1), E_lam (_,ty2,bod2) ->
          expr_eq ty1 ty2 && expr_eq bod1 bod2
        | E_arrow(a1,b1), E_arrow(a2,b2) ->
          expr_eq a1 a2 && expr_eq b1 b2
        | (E_kind | E_type | E_const _ | E_var _ | E_bound_var _
          | E_app _ | E_lam _ | E_arrow _), _ -> false
      end

    let hash e : int =
      match e.e_view with
      | E_kind -> 11
      | E_type -> 12
      | E_const (c,l) ->
        H.combine4 20 (Name.hash c.c_name) (expr_hash c.c_ty) (H.list expr_hash l)
      | E_var v -> H.combine2 30 (var_hash v)
      | E_bound_var v -> H.combine3 40 (H.int v.bv_idx) (expr_hash v.bv_ty)
      | E_app (f,a) -> H.combine3 50 (expr_hash f) (expr_hash a)
      | E_lam (_,ty,bod) ->
        H.combine3 60 (expr_hash ty) (expr_hash bod)
      | E_arrow (a,b) -> H.combine3 80 (expr_hash a) (expr_hash b)

    let set_id t id =
      assert (t.e_id == -1);
      t.e_id <- id

    let on_new e = ignore (Lazy.force e.e_ty : _ option)
    end)

type const_kind = C_ty | C_term

(* special map for indexing constants, differentiating type and term constants *)
module Str_k_map = CCMap.Make(struct
    type t = const_kind * string
    let compare (k1,c1)(k2,c2) =
      if k1=k2 then String.compare c1 c2 else CCOrd.compare k1 k2
  end)

type thm = {
  th_concl: expr;
  th_hyps: Expr_set.t;
  mutable th_flags: int; (* [bool flags|ctx uid] *)
  mutable th_theory: theory option;
}
(* TODO:
   - store set of axioms used
   *)

and theory = {
  theory_name: Name.t;
  theory_ctx: ctx;
  mutable theory_in_constants: const Str_k_map.t;
  mutable theory_in_theorems: thm list;
  mutable theory_defined_constants: const Str_k_map.t;
  mutable theory_defined_theorems: thm list;
}

and ctx = {
  ctx_uid: int;
  ctx_exprs: Expr_hashcons.t;
  ctx_consts: Const_hashcons.t;
  ctx_kind: expr lazy_t;
  ctx_type: expr lazy_t;
  ctx_bool: expr lazy_t;
  ctx_bool_c: const lazy_t;
  ctx_eq_c: const lazy_t;
  ctx_select_c : const lazy_t;
  mutable ctx_axioms: thm list;
  mutable ctx_axioms_allowed: bool;
}
(* TODO: derived rules and named rules/theorems *)

let[@inline] thm_ctx_uid th : int = th.th_flags land ctx_id_mask

let[@inline] ctx_check_e_uid ctx (e:expr) = assert (ctx.ctx_uid == expr_ctx_uid e)
let[@inline] ctx_check_th_uid ctx (th:thm) = assert (ctx.ctx_uid == thm_ctx_uid th)

let id_bool = Name.make "bool"
let id_eq = Name.make "="
let id_select = Name.make "select"

module Const = struct
  type t = const
  let[@inline] pp out c = Name.pp out c.c_name
  let[@inline] to_string c = Fmt.to_string pp c
  let[@inline] def_loc c = c.c_def_loc
  let[@inline] name c = c.c_name
  let[@inline] equal c1 c2 = Name.equal c1.c_name c2.c_name

  type args = const_args =
    | C_ty_vars of ty_var list
    | C_arity of int
  let[@inline] args c = c.c_args
  let[@inline] ty c = c.c_ty

  let pp_args out = function
    | C_arity n -> Fmt.fprintf out "/%d" n
    | C_ty_vars vs -> Fmt.fprintf out " %a" (Fmt.Dump.list var_pp) vs

  let pp_with_ty out c =
    Fmt.fprintf out "`@[%a%a@ : %a@]`"
      Name.pp c.c_name pp_args c.c_args expr_pp_ c.c_ty

  let[@inline] eq ctx = Lazy.force ctx.ctx_eq_c
  let[@inline] bool ctx = Lazy.force ctx.ctx_bool_c
  let[@inline] select ctx = Lazy.force ctx.ctx_select_c
  let is_eq_to_bool c = Name.equal c.c_name id_bool
  let is_eq_to_eq c = Name.equal c.c_name id_bool

  let[@inline] make_ ctx (c:t) : t =
    Const_hashcons.hashcons ctx.ctx_consts c
end

module Var = struct
  type t = var

  let[@inline] name v = v.v_name
  let[@inline] ty v = v.v_ty
  let[@inline] map_ty v ~f = {v with v_ty=f v.v_ty}
  let make v_name v_ty : t = {v_name; v_ty}
  let makef fmt ty = Fmt.kasprintf (fun s->make s ty) fmt
  let equal = var_eq
  let hash = var_hash
  let pp = var_pp
  let pp_with_ty out v =
    Fmt.fprintf out "(@[%s :@ %a@])" v.v_name expr_pp_ v.v_ty
  let to_string = Fmt.to_string pp
  let compare a b : int =
    if expr_eq a.v_ty b.v_ty
    then String.compare a.v_name b.v_name
    else expr_compare a.v_ty b.v_ty

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = CCSet.Make(AsKey)
  module Tbl = CCHashtbl.Make(AsKey)
end

type subst = {
  ty: expr Var.Map.t; (* ty subst *)
  m: expr Var.Map.t; (* term subst *)
}

module BVar = struct
  type t = bvar
  let make i ty : t = {bv_idx=i; bv_ty=ty}
  let pp out v = Fmt.fprintf out "db_%d" v.bv_idx
  let to_string = Fmt.to_string pp
end

module type EXPR = sig
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * t list
    | E_app of t * t
    | E_lam of string * expr * expr
    | E_arrow of expr * expr

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t

  val view : t -> view
  val ty : t -> ty option
  val ty_exn : t -> ty
  val is_closed : t -> bool
  val is_eq_to_type : t -> bool
  val is_eq_to_bool : t -> bool
  val is_a_bool : t -> bool
  val is_a_type : t -> bool
  (** Is the type of [e] equal to [Type]? *)

  val iter : f:(bool -> t -> unit) -> t -> unit
  val exists : f:(bool -> t -> bool) -> t -> bool
  val for_all : f:(bool -> t -> bool) -> t -> bool

  val contains : t -> sub:t -> bool
  val free_vars : ?init:Var.Set.t -> t -> Var.Set.t
  val free_vars_iter : t -> var Iter.t

  val unfold_app : t -> t * t list
  val unfold_eq : t -> (t * t) option
  val unfold_arrow : t -> t list * t
  val return_ty : t -> t
  val as_const : t -> (Const.t * ty list) option
  val as_const_exn : t -> Const.t * ty list

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t

  val iter_dag : f:(t -> unit) -> t -> unit

  type 'a with_ctx

  val subst : (recursive:bool -> t -> subst -> t) with_ctx

  val type_ : (t) with_ctx
  val bool : (t) with_ctx
  val eq : (ty -> t) with_ctx
  val select : (ty -> t) with_ctx
  val var : (var -> t) with_ctx
  val const : (const -> ty list -> t) with_ctx
  val new_const : (?def_loc:location -> string -> ty_var list -> ty -> const) with_ctx
  val new_ty_const : (?def_loc:location -> string -> int -> const) with_ctx
  val var_name : (string -> ty -> t) with_ctx
  val bvar : (int -> ty -> t) with_ctx
  val app : (t -> t -> t) with_ctx
  val app_l : (t -> t list -> t) with_ctx
  val app_eq : (t -> t -> t) with_ctx
  val lambda : (var -> t -> t) with_ctx
  val lambda_l : (var list -> t -> t) with_ctx
  val lambda_db : (name:string -> ty_v:ty -> t -> t) with_ctx
  val arrow : (t -> t -> t) with_ctx
  val arrow_l : (t list -> t -> t) with_ctx

  val map : (f:(bool -> t -> t) -> t -> t) with_ctx

  val db_shift: (t -> int -> t) with_ctx
  val open_lambda : (t -> (var * t) option) with_ctx
  val open_lambda_exn : (t -> var * t) with_ctx
end

module Expr = struct
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * expr list
    | E_app of t * t
    | E_lam of string * t * t
    | E_arrow of t * t

  let[@inline] ty e = Lazy.force e.e_ty
  let[@inline] view e = e.e_view
  let[@inline] ty_exn e = match e.e_ty with
    | lazy None -> assert false
    | lazy (Some ty) -> ty

  let equal = expr_eq
  let hash = expr_hash

  let pp = expr_pp_
  let to_string = Fmt.to_string pp

  let compare = expr_compare
  let db_depth = expr_db_depth
  let has_fvars = expr_has_fvars

  let[@inline] iter ~f (e:t) : unit =
    match view e with
    | E_kind | E_type | E_const _ -> ()
    | _ ->
      CCOpt.iter (f false) (ty e);
      match view e with
      | E_kind | E_type | E_const _ -> assert false
      | E_var v -> f false v.v_ty
      | E_bound_var v -> f false v.bv_ty
      | E_app (hd,a) -> f false hd; f false a
      | E_lam (_, tyv, bod) -> f false tyv; f true bod
      | E_arrow (a,b) -> f false a; f false b

  exception E_exit

  let[@inline] exists ~f e : bool =
    try
      iter e ~f:(fun b x -> if f b x then raise_notrace E_exit); false
    with E_exit -> true

  let[@inline] for_all ~f e : bool =
    try
      iter e ~f:(fun b x -> if not (f b x) then raise_notrace E_exit); true
    with E_exit -> false

  let[@inline] is_closed e : bool = db_depth e == 0

  let compute_db_depth_ e : int =
    let d1 = match ty e with
      | None -> 0
      | Some d -> db_depth d
    in
    let d2 = match view e with
      | E_kind | E_type | E_const _ | E_var _ -> 0
      | E_bound_var v -> v.bv_idx+1
      | E_app (a,b) | E_arrow (a,b) -> max (db_depth a) (db_depth b)
      | E_lam (_, ty,bod) ->
        max (db_depth ty) (max 0 (db_depth bod - 1))
    in
    max d1 d2

  let compute_has_fvars_ e : bool =
    begin match ty e with
      | None -> false
      | Some ty -> has_fvars ty
    end ||
    begin match view e with
      | E_var _ -> true
      | E_kind | E_type | E_bound_var _ -> false
      | E_const (_, args) -> List.exists has_fvars args
      | E_app (a,b) | E_arrow (a,b) -> has_fvars a || has_fvars b
      | E_lam (_,ty,bod) -> has_fvars ty || has_fvars bod
    end

  (* hashconsing + computing metadata *)
  let make_ (ctx:ctx) view ty : t =
    let e = { e_view=view; e_ty=ty; e_id= -1; e_flags=0 } in
    let e_h = Expr_hashcons.hashcons ctx.ctx_exprs e in
    if e == e_h then (
      (* new term, compute metadata *)
      assert ((ctx.ctx_uid land ctx_id_mask) == ctx.ctx_uid);
      let has_fvars = compute_has_fvars_ e in
      e_h.e_flags <-
        ((compute_db_depth_ e) lsl (1+ctx_id_bits))
        lor (if has_fvars then 1 lsl ctx_id_bits else 0)
        lor ctx.ctx_uid;
      ctx_check_e_uid ctx e_h;
    );
    e_h

  let kind ctx = Lazy.force ctx.ctx_kind
  let type_ ctx = Lazy.force ctx.ctx_type

  let[@inline] is_eq_to_type e = match view e with | E_type -> true | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty_exn e)
  let is_eq_to_bool e =
    match view e with E_const (c,[]) -> Name.equal c.c_name id_bool | _ -> false
  let is_a_bool e = is_eq_to_bool (ty_exn e)

  let bool ctx = Lazy.force ctx.ctx_bool

  let var ctx v : t =
    ctx_check_e_uid ctx v.v_ty;
    make_ ctx (E_var v) (Lazy.from_val (Some v.v_ty))

  let var_name ctx s ty : t = var ctx {v_name=s; v_ty=ty}

  let bvar ctx i ty : t =
    assert (i>=0);
    ctx_check_e_uid ctx ty;
    make_ ctx (E_bound_var {bv_idx=i; bv_ty=ty}) (Lazy.from_val (Some ty))

  (* map immediate subterms *)
  let[@inline] map ctx ~f (e:t) : t =
    match view e with
    | E_kind | E_type | E_const (_,[]) -> e
    | _ ->
      let ty' = lazy (
        match e.e_ty with
        | lazy None -> None
        | lazy (Some ty) -> Some (f false ty)
      ) in
      begin match view e with
        | E_var v ->
          let v_ty = f false v.v_ty in
          if v_ty == v.v_ty then e
          else make_ ctx (E_var {v with v_ty}) ty'
        | E_const (c,args) ->
          let args' = List.map (f false) args in
          if List.for_all2 equal args args'
          then e
          else make_ ctx (E_const (c,args')) ty'
        | E_bound_var v ->
          let ty' = f false v.bv_ty in
          if v.bv_ty == ty' then e
          else make_ ctx (E_bound_var {v with bv_ty=ty'}) (Lazy.from_val (Some ty'))
        | E_app (hd,a) ->
          let hd' =  f false hd in
          let a' =  f false a in
          if a==a' && hd==hd' then e
          else make_ ctx (E_app (f false hd, f false a)) ty'
        | E_lam (n, tyv, bod) ->
          let tyv' = f false tyv in
          let bod' = f true bod in
          if tyv==tyv' && bod==bod' then e
          else make_ ctx (E_lam (n, tyv', bod')) ty'
        | E_arrow (a,b) ->
          let a' = f false a in
          let b' = f false b in
          if a==a' && b==b' then e
          else make_ ctx (E_arrow (a', b')) ty'
        | E_kind | E_type -> assert false
      end

  exception IsSub

  let contains e ~sub : bool =
    let rec aux e =
      if equal e sub then raise_notrace IsSub;
      iter e ~f:(fun _ u -> aux u)
    in
    try aux e; false with IsSub -> true

  let free_vars_iter e : var Iter.t =
    fun yield ->
      let rec aux e =
        match view e with
        | E_var v -> yield v; aux (Var.ty v)
        | E_const (_, args) -> List.iter aux args
        | _ -> iter e ~f:(fun _ u -> aux u)
      in
      aux e

  let free_vars ?(init=Var.Set.empty) e : Var.Set.t =
    let set = ref init in
    free_vars_iter e (fun v -> set := Var.Set.add v !set);
    !set

  let id_gen_ = ref 0 (* note: updated atomically *)

  let new_const_ ctx ?def_loc ?in_theory
      name args ty : const =
    let c_def_id = match in_theory with
      | Some th -> C_in_theory th.theory_name
      | None -> incr id_gen_; C_def_gen !id_gen_
    in
    let c = {
      c_name=name; c_def_id; c_ty=ty; c_args=args;
      c_def_loc=def_loc;
    } in
    Const.make_ ctx c

  let new_const ctx ?def_loc name ty_vars ty : const =
    let fvars = free_vars ty in
    let diff = Var.Set.diff fvars (Var.Set.of_list ty_vars) in
    begin match Var.Set.choose_opt diff with
      | None -> ()
      | Some v ->
        errorf
          (fun k->k
              "Kernel.new_const: type variable %a@ \
               occurs in type of the constant `%s`,@ \
               but not in the type variables %a"
              Var.pp v name (Fmt.Dump.list Var.pp) ty_vars);
    end;
    let name = Name.make name in
    new_const_ ctx ?def_loc name (C_ty_vars ty_vars) ty

  let new_ty_const ctx ?def_loc name n : ty_const =
    let name = Name.make name in
    new_const_ ctx name ?def_loc (C_arity n) (type_ ctx)

  let mk_const_ ctx c args ty : t =
    make_ ctx (E_const (c,args)) ty

  let subst_empty_ : subst =
    {ty=Var.Map.empty;
     m=Var.Map.empty;
    }

  let subst_pp_ out (self:subst) : unit =
    if Var.Map.is_empty self.m && Var.Map.is_empty self.ty then (
      Fmt.string out "{}"
    ) else (
      let pp_b out (v,t) =
        Fmt.fprintf out "(@[%a := %a@])" Var.pp_with_ty v expr_pp_ t
      in
      Fmt.fprintf out "@[<hv>{@,%a@,}@]"
        (pp_iter ~sep:" " pp_b)
        (Iter.append (Var.Map.to_iter self.ty) (Var.Map.to_iter self.m))
    )

  (* Bind a variable into a substitution. *)
  let subst_bind_ (subst:subst) v t : subst =
    if is_eq_to_type v.v_ty then (
      { subst with ty=Var.Map.add v t subst.ty }
    ) else (
      { subst with m=Var.Map.add v t subst.m;  }
    )

  let db_shift ctx (e:t) (n:int) =
    ctx_check_e_uid ctx e;
    assert (CCOpt.for_all is_closed (Lazy.force e.e_ty));
    let rec loop e k : t =
      if is_closed e then e
      else if is_a_type e then e
      else (
        match view e with
        | E_bound_var bv ->
          if bv.bv_idx >= k
          then bvar ctx (bv.bv_idx + n) bv.bv_ty
          else bvar ctx bv.bv_idx bv.bv_ty
        | _ ->
          map ctx e ~f:(fun inbind u -> loop u (if inbind then k+1 else k))
      )
    in
    assert (n >= 0);
    if n = 0 then e else loop e 0

  module E_int_tbl = CCHashtbl.Make(struct
      type t = expr * int
      let equal (t1,k1) (t2,k2) = equal t1 t2 && k1==k2
      let hash (t,k) = H.combine3 27 (hash t) (H.int k)
    end)

  let subst_ ctx ~recursive e0 (subst:subst) : t =
    (* cache for types and some terms *)
    let cache_ = E_int_tbl.create 16 in
    let ty_subst_empty_ = Var.Map.is_empty subst.ty in

    let rec loop k e =
      if is_a_type e then (
        (* type subst: can use a cache, and only consider subst.ty
           with k=0 since there are no binders *)
        if ty_subst_empty_ then e
        else (
          try E_int_tbl.find cache_ (e,0)
          with Not_found ->
            let r = loop_uncached_ 0 e in
            E_int_tbl.add cache_ (e,0) r;
            r
        )
      ) else (
        try E_int_tbl.find cache_ (e,k)
        with Not_found ->
          let r = loop_uncached_ k e in
          E_int_tbl.add cache_ (e,k) r;
          r
      )

    and loop_uncached_ k (e:t) : t =
      let ty = lazy (
        match e.e_ty with
        | lazy None -> None
        | lazy (Some ty) -> Some (loop 0 ty)
      ) in
      match view e with
      | _ when not (has_fvars e) -> e (* nothing to subst in *)
      | E_var v when is_eq_to_type v.v_ty ->
        (* type variable substitution *)
        begin match Var.Map.find v subst.ty with
          | u ->
            assert (is_closed u); if recursive then loop 0 u else u
          | exception Not_found -> var ctx v
        end
      | E_var v ->
        (* first, subst in type *)
        let v = {v with v_ty=loop k v.v_ty} in
        begin match Var.Map.find v subst.m with
          | u ->
            let u = db_shift ctx u k in
            if recursive then loop 0 u else u
          | exception Not_found -> var ctx v
        end
      | E_const (_, []) -> e
      | E_const (c, args) ->
        (* subst in args, thus changing the whole term's type *)
        let ty = lazy (Some (loop k (ty_exn e))) in
        mk_const_ ctx c (List.map (loop k) args) ty
      | E_app (hd, a) ->
        let hd' = loop k hd in
        let a' = loop k a in
        if hd==hd' && a'==a then e
        else make_ ctx (E_app (hd',a')) ty
      | E_arrow (a, b) ->
        let a' = loop k a in
        let b' = loop k b in
        if a==a' && b'==b then e
        else make_ ctx (E_arrow (a',b')) ty
      | _ ->
        map ctx e ~f:(fun inb u -> loop (if inb then k+1 else k) u)
    in

    if Var.Map.is_empty subst.m && Var.Map.is_empty subst.ty then (
      e0
    ) else (
      loop 0 e0
    )

  let[@inline] subst ctx ~recursive e subst =
    subst_ ctx ~recursive e subst

  let const ctx c args : t =
    ctx_check_e_uid ctx c.c_ty;
    let ty =
      match c.c_args with
      | C_arity n ->
        if List.length args <> n then (
          errorf
            (fun k->k"constant %a requires %d arguments, but is applied to %d"
                Name.pp c.c_name
                n (List.length args));
        );
        Lazy.from_val (Some c.c_ty)
      | C_ty_vars ty_vars ->
        if List.length args <> List.length ty_vars then (
          errorf
            (fun k->k"constant %a requires %d arguments, but is applied to %d"
                Name.pp c.c_name
                (List.length ty_vars) (List.length args));
        );
        lazy (
          let sigma = List.fold_left2 subst_bind_ subst_empty_ ty_vars args in
          Some (subst ~recursive:false ctx c.c_ty sigma)
        )
    in
    mk_const_ ctx c args ty

  let eq ctx ty =
    let eq = Lazy.force ctx.ctx_eq_c in
    const ctx eq [ty]

  let select ctx ty =
    let sel = Lazy.force ctx.ctx_select_c in
    const ctx sel [ty]

  let abs_on_ ctx (v:var) (e:t) : t =
    ctx_check_e_uid ctx v.v_ty;
    ctx_check_e_uid ctx e;
    if not (is_closed v.v_ty) then (
      errorf (fun k->k"cannot abstract on variable with non closed type %a" pp v.v_ty)
    );
    let db0 = bvar ctx 0 v.v_ty in
    let body = db_shift ctx e 1 in
    subst ~recursive:false ctx body {m=Var.Map.singleton v db0; ty=Var.Map.empty}

  (* replace DB0 in [e] with [u] *)
  let subst_db_0 ctx e ~by:u : t =
    ctx_check_e_uid ctx e;
    ctx_check_e_uid ctx u;

    let cache_ = E_int_tbl.create 8 in

    let rec aux e k : t =
      if is_a_type e then e
      else if db_depth e < k then e
      else (
        match view e with
        | E_const _ -> e
        | E_bound_var bv when bv.bv_idx = k ->
          (* replace here *)
          db_shift ctx u k
        | _ ->
          (* use the cache *)
          try E_int_tbl.find cache_ (e,k)
          with Not_found ->
            let r =
              map ctx e ~f:(fun inb u -> aux u (if inb then k+1 else k))
            in
            E_int_tbl.add cache_ (e,k) r;
            r
      )
    in
    if is_closed e then e else aux e 0

  (* find a name that doesn't capture a variable of [e] *)
  let pick_name_ (name0:string) (e:t) : string =
    let rec loop i =
      let name = if i= 0 then name0 else Printf.sprintf "%s%d" name0 i in
      if free_vars_iter e |> Iter.exists (fun v -> v.v_name = name)
      then loop (i+1)
      else name
    in
    loop 0

  let open_lambda ctx e : _ option =
    match view e with
    | E_lam (name, ty, bod) ->
      let name = pick_name_ name bod in
      let v = Var.make name ty in
      let bod' = subst_db_0 ctx bod ~by:(var ctx v) in
      Some (v, bod')
    | _ -> None

  let open_lambda_exn ctx e = match open_lambda ctx e with
    | Some tup -> tup
    | None -> errorf (fun k->k"open-lambda: term is not a lambda:@ %a" pp e)

  let arrow ctx a b : t =
    if not (is_a_type a) || not (is_a_type b) then (
      errorf (fun k->k"arrow: both arguments must be types");
    );
    let ty = Lazy.from_val (Some (type_ ctx)) in
    make_ ctx (E_arrow (a,b)) ty

  let app ctx f a : t =
    ctx_check_e_uid ctx f;
    ctx_check_e_uid ctx a;

    let ty_f = ty_exn f in
    let ty_a = ty_exn a in

    let[@inline never] fail () =
      errorf
        (fun k->
          k"@[<2>kernel: cannot apply function@ `@[%a@]`@ \
           to argument `@[%a@]`@]@];@ \
           @[function has type@ `@[%a@]`,@ \
           but arg has type `@[%a@]`@]"
           pp f pp a pp ty_f pp ty_a)
    in

    let ty =
      match view ty_f with
      | E_arrow (ty_arg, ty_ret) when equal ty_arg ty_a ->
        ty_ret (* no instantiation needed *)
      | _ -> fail()
    in
    let ty = Lazy.from_val (Some ty) in
    let e = make_ ctx (E_app (f,a)) ty in
    e

  let rec app_l ctx f l = match l with
    | [] -> f
    | x :: l' ->
      let f = app ctx f x in
      app_l ctx f l'

  let app_eq ctx a b =
    let f = eq ctx (ty_exn a) in
    let f = app ctx f a in
    let f = app ctx f b in
    f

  let arrow_l ctx l ret : t = CCList.fold_right (arrow ctx) l ret

  let lambda_db ctx ~name ~ty_v bod : t =
    ctx_check_e_uid ctx ty_v;
    ctx_check_e_uid ctx bod;
    if not (is_a_type ty_v) then (
      errorf (fun k->k"lambda: variable must have a type as type, not %a"
                 pp ty_v);
    );
    let ty = lazy (
      (* type of [λx:a. t] is [a -> typeof(t)] if [a] is a type *)
      Some (arrow ctx ty_v (ty_exn bod))
    ) in
    make_ ctx (E_lam (name, ty_v, bod)) ty

  let lambda ctx v bod =
    let bod = abs_on_ ctx v bod in
    lambda_db ctx ~name:v.v_name ~ty_v:v.v_ty bod

  let lambda_l ctx = CCList.fold_right (lambda ctx)

  let unfold_app = unfold_app

  let[@inline] unfold_eq e =
    let f, l = unfold_app e in
    match view f, l with
    | E_const ({c_name;_}, [_]), [a;b] when Name.equal c_name id_eq -> Some(a,b)
    | _ -> None

  let[@unroll 1] rec unfold_arrow e =
    match view e with
    | E_arrow (a,b) ->
      let args, ret = unfold_arrow b in
      a::args, ret
    | _ -> [], e

  let[@unroll 1] rec return_ty e =
    match view e with
    | E_arrow (_,b) -> return_ty b
    | _ -> e

  let[@inline] as_const e = match e.e_view with
    | E_const (c,args) -> Some (c,args)
    | _ -> None

  let[@inline] as_const_exn e = match e.e_view with
    | E_const (c,args) -> c, args
    | _ -> errorf (fun k->k"%a is not a constant" pp e)

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = Expr_set
  module Tbl = CCHashtbl.Make(AsKey)

  let iter_dag ~f e : unit =
    let tbl = Tbl.create 8 in
    let rec loop e =
      if not (Tbl.mem tbl e) then (
        Tbl.add tbl e ();
        f e;
        iter e ~f:(fun _ u -> loop u)
      )
    in
    loop e
end

module type EXPR_FOR_CTX = EXPR
  with type 'a with_ctx := 'a
   and module Tbl = Expr.Tbl
     and module Set = Expr.Set
     and module Map = Expr.Map

let make_expr (ctx: ctx) : (module EXPR_FOR_CTX) =
  let module M = struct
    include Expr
    let subst = subst ctx
    let type_ = type_ ctx
    let bool = bool ctx
    let eq = eq ctx
    let select = select ctx
    let var = var ctx
    let const = const ctx
    let new_const = new_const ctx
    let new_ty_const = new_ty_const ctx
    let bvar = bvar ctx
    let var_name = var_name ctx
    let app = app ctx
    let app_l = app_l ctx
    let app_eq = app_eq ctx
    let lambda = lambda ctx
    let lambda_l = lambda_l ctx
    let lambda_db = lambda_db ctx
    let arrow = arrow ctx
    let arrow_l = arrow_l ctx
    let map = map ctx
    let db_shift = db_shift ctx
    let open_lambda = open_lambda ctx
    let open_lambda_exn = open_lambda_exn ctx
  end in
  (module M)

(* TODO: write Expr_for_ctx; then use it in tests *)

module Subst = struct
  type t = subst = {
    ty: expr Var.Map.t; (* ty subst *)
    m: expr Var.Map.t; (* term subst *)
  }

  let[@inline] is_empty self =
    Var.Map.is_empty self.ty &&
    Var.Map.is_empty self.m
  let[@inline] find_exn x s =
    if Expr.is_eq_to_type x.v_ty then Var.Map.find x s.ty
    else Var.Map.find x s.m

  let[@inline] mem x s =
    if Expr.is_eq_to_type x.v_ty then Var.Map.mem x s.ty
    else Var.Map.mem x s.m
  let empty = Expr.subst_empty_
  let bind = Expr.subst_bind_
  let pp = Expr.subst_pp_
  let[@inline] bind' x t s : t = bind s x t
  let[@inline] size self = Var.Map.cardinal self.m + Var.Map.cardinal self.ty
  let[@inline] to_iter self =
    Iter.append (Var.Map.to_iter self.m) (Var.Map.to_iter self.ty)
  let to_string = Fmt.to_string pp

  let is_renaming (self:t) : bool =
    let is_renaming_ m =
      try
        let codom =
          Var.Map.fold
            (fun _v e acc -> match Expr.view e with
               | E_var u -> Var.Set.add u acc
               | _ -> raise_notrace Exit) m Var.Set.empty
        in
        Var.Set.cardinal codom = Var.Map.cardinal m
      with Exit -> false
    in
    is_renaming_ self.ty && is_renaming_ self.m

  let[@inline] bind_uncurry_ s (x,t) = bind s x t
  let of_list = List.fold_left bind_uncurry_ empty
  let of_iter = Iter.fold bind_uncurry_ empty
end

(*$inject
  let ctx = Ctx.create ()
  let bool = Expr.bool ctx
  let type_ = Expr.type_ ctx
  let tau = Expr.const ctx (Expr.new_ty_const ctx "tau" 0) []
  let lambda v t = Expr.lambda ctx v t
  let v' s ty = Var.make s ty
  let v x = Expr.var ctx x
  let (@->) a b = Expr.arrow ctx a b
  let (@@) a b = Expr.app ctx a b
  let a = Expr.const ctx (Expr.new_const ctx "a0" [] tau) []
  let b = Expr.const ctx (Expr.new_const ctx "b0" [] tau) []
  let c = Expr.const ctx (Expr.new_const ctx "c0" [] tau) []
  let f1: const = Expr.new_const ctx "f1" [] (tau @-> tau)
  let eq = Expr.app_eq ctx

  let must_fail f = try ignore (f()); false with _ -> true
*)

(*$T
  must_fail (fun() -> a @-> b)
  Expr.equal (tau @-> bool) (tau @-> bool)
*)


(** {2 Toplevel goals} *)
module Goal = struct
  type t = {
    hyps: Expr.Set.t;
    concl: Expr.t;
  }

  let make hyps concl : t = {hyps; concl}
  let make_l h c = make (Expr.Set.of_list h) c
  let make_nohyps c : t = make Expr.Set.empty c

  let[@inline] concl g = g.concl
  let[@inline] hyps g = g.hyps
  let[@inline] hyps_iter g = Expr.Set.to_iter g.hyps

  let pp out (self:t) : unit =
    if Expr.Set.is_empty self.hyps then (
      Fmt.fprintf out "@[?-@ %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[<hv>%a@ ?-@ %a@]"
        (pp_iter ~sep:", " Expr.pp) (hyps_iter self)
        Expr.pp self.concl
    )
  let to_string = Fmt.to_string pp
end

(** {2 Context}

    The context is storing the term state, list of axioms,
    and other parameters.
    Terms from distinct contexts must never be mixed. *)
module Ctx = struct
  type t = ctx

  let uid_ = ref 0

  let create () : t =
    let ctx_uid = !uid_ land ctx_id_mask in
    incr uid_;
    let rec ctx = {
      ctx_uid;
      ctx_exprs=Expr_hashcons.create ~size:2_048 ();
      ctx_consts=Const_hashcons.create ~size:32 ();
      ctx_axioms=[];
      ctx_axioms_allowed=true;
      ctx_kind=lazy (Expr.make_ ctx E_kind (Lazy.from_val None));
      ctx_type=lazy (
        let kind = Expr.kind ctx in
        Expr.make_ ctx E_type (Lazy.from_val (Some kind))
      );
      ctx_bool_c=lazy (
        let typ = Expr.type_ ctx in
        Expr.new_const_ ctx id_bool (C_arity 0) typ
      );
      ctx_bool=lazy (
        Expr.const ctx (Lazy.force ctx.ctx_bool_c) []
      );
      ctx_eq_c=lazy (
        let type_ = Expr.type_ ctx in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx ea @@ arrow ctx ea @@ bool ctx) in
        Expr.new_const_ ctx id_eq (C_ty_vars [a_]) typ
      );
      ctx_select_c=lazy (
        let type_ = Expr.type_ ctx in
        let lazy bool_ = ctx.ctx_bool in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx (arrow ctx ea bool_) ea) in
        Expr.new_const_ ctx id_select (C_ty_vars [a_]) typ
      );
    } in
    ctx

  let pledge_no_more_axioms self =
    if self.ctx_axioms_allowed then (
      Log.debugf 5 (fun k->k "pledge no more axioms");
      self.ctx_axioms_allowed <- false;
    )

  let axioms self k = List.iter k self.ctx_axioms
end

module New_ty_def = struct
  type t = {
    tau: ty_const;
    (** the new type constructor *)
    fvars: var list;
    c_abs: const;
    (** Function from the general type to `tau` *)
    c_repr: const;
    (** Function from `tau` back to the general type *)
    abs_thm: thm;
    (** `abs_thm` is `|- abs (repr x) = x` *)
    abs_x: var;
    repr_thm: thm;
    (** `repr_thm` is `|- Phi x <=> repr (abs x) = x` *)
    repr_x: var;
  }
end

(** {2 Theorems and Deduction Rules} *)

module type THM = sig
  type 'a with_ctx

  type t = thm

  include Sigs.PP with type t := t
  val pp_quoted : t Fmt.printer
  val concl : t -> expr
  val hyps_iter : t -> expr iter
  val hyps_l : t -> expr list
  val hyps_sorted_l : t -> expr list
  val n_hyps : t -> int
  val has_hyps : t -> bool
  val is_proof_of : t -> Goal.t -> bool
  val assume : (expr -> t) with_ctx
  val axiom : (expr list -> expr -> t) with_ctx
  val cut : (t -> t -> t) with_ctx
  val refl : (expr -> t) with_ctx
  val congr : (t -> t -> t) with_ctx
  val subst : recursive:bool -> (t -> Subst.t -> t) with_ctx
  val sym : (t -> t) with_ctx
  val trans : (t -> t -> t) with_ctx
  val bool_eq : (t -> t -> t) with_ctx
  val bool_eq_intro : (t -> t -> t) with_ctx
  val beta_conv : (expr -> t) with_ctx
  val abs : (var -> t -> t) with_ctx
  val new_basic_definition :
    (?def_loc:location -> expr -> t * const) with_ctx
  val new_basic_type_definition :
    (?ty_vars:ty_var list ->
    name:string ->
    abs:string ->
    repr:string ->
    thm_inhabited:thm ->
    unit ->
    New_ty_def.t) with_ctx
end

module Thm = struct
  type t = thm

  let[@inline] concl self = self.th_concl
  let[@inline] hyps_ self = self.th_hyps
  let[@inline] hyps_iter self k = Expr_set.iter k self.th_hyps
  let[@inline] hyps_l self = Expr_set.elements self.th_hyps
  let hyps_sorted_l = hyps_l
  let[@inline] has_hyps self = not (Expr_set.is_empty self.th_hyps)
  let n_hyps self = Expr_set.cardinal self.th_hyps

  let pp out (th:t) =
    if has_hyps th then (
      Fmt.fprintf out "@[<hv1>%a@;<1 -1>|-@ %a@]" (pp_list ~sep:", " Expr.pp) (hyps_l th)
        Expr.pp (concl th)
    ) else (
      Fmt.fprintf out "@[<1>|-@ %a@]" Expr.pp (concl th)
    )

  let to_string = Fmt.to_string pp
  let pp_quoted = Fmt.within "`" "`" pp

  let is_proof_of self (g:Goal.t) : bool =
    Expr.equal self.th_concl (Goal.concl g) &&
    Expr_set.subset self.th_hyps (Goal.hyps g)

  (** {3 Deduction rules} *)

  let make_ ctx hyps concl : t =
    let th_flags = ctx.ctx_uid in
    { th_flags; th_concl=concl; th_hyps=hyps; th_theory=None }

  let is_bool_ ctx e : bool =
    let ty = Expr.ty_exn e in
    Expr.equal (Expr.bool ctx) ty

  let[@inline] wrap_exn k f =
    try f()
    with e ->
      errorf ~src:e k

  let assume ctx (e:Expr.t) : t =
    wrap_exn (fun k->k"in assume `@[%a@]`:" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    if not (is_bool_ ctx e) then (
      error "assume takes a boolean"
    );
    make_ ctx (Expr.Set.singleton e) e

  let axiom ctx hyps e : t =
    wrap_exn (fun k->
        let g = Goal.make_l hyps e in
        k"in axiom `@[%a@]`:" Goal.pp g)
    @@ fun () ->
    ctx_check_e_uid ctx e;
    if not ctx.ctx_axioms_allowed then (
      error "the context does not accept new axioms, see `pledge_no_more_axioms`"
    );
    if not (is_bool_ ctx e && List.for_all (is_bool_ ctx) hyps) then (
      error "axiom takes a boolean"
    );
    make_ ctx (Expr.Set.of_list hyps) e

  let merge_hyps_ = Expr.Set.union

  let cut ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in cut@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let b = concl th1 in
    let hyps = merge_hyps_ (hyps_ th1) (Expr.Set.remove b (hyps_ th2)) in
    make_ ctx hyps (concl th2)

  let refl ctx e : t =
    ctx_check_e_uid ctx e;
    make_ ctx Expr.Set.empty (Expr.app_eq ctx e e)

  let congr ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in congr@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
    | None, _ -> error "th1 is non equational"
    | _, None -> error "th2 is non equational"
    | Some (f,g), Some (t,u) ->
      let t1 = Expr.app ctx f t in
      let t2 = Expr.app ctx g u in
      let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
      make_ ctx hyps (Expr.app_eq ctx t1 t2)

  exception E_subst_non_closed of var * expr

  let subst ~recursive ctx th s : t =
    begin try
        Var.Map.iter (fun v t ->
            if not (Expr.is_closed t) then raise_notrace (E_subst_non_closed (v,t)))
          s.m
      with
      | E_subst_non_closed (v,t) ->
        errorf(fun k->k"subst: variable %a@ is bound to non-closed term %a"
                  Var.pp v Expr.pp t)
    end;
    let hyps = hyps_ th |> Expr.Set.map (fun e -> Expr.subst ~recursive ctx e s) in
    let concl = Expr.subst ~recursive ctx (concl th) s in
    make_ ctx hyps concl

  let sym ctx th : t =
    wrap_exn (fun k->k"@[<2>in sym@ `@[%a@]`@]:" pp th) @@ fun () ->
    ctx_check_th_uid ctx th;
    match Expr.unfold_eq (concl th) with
    | None -> errorf (fun k->k"sym: concl of %a@ should be an equation" pp th)
    | Some (t,u) ->
      make_ ctx (hyps_ th) (Expr.app_eq ctx u t)

  let trans ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in trans@ %a@ %a@]:" pp_quoted th1 pp_quoted th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
    | None, _ -> errorf (fun k->k"trans: concl of %a@ should be an equation" pp th1)
    | _, None -> errorf (fun k->k"trans: concl of %a@ should be an equation" pp th2)
    | Some (t,u), Some (u',v) ->
      if not (Expr.equal u u') then (
        errorf (fun k->k"@[<2>kernel: trans: conclusions@ \
                         of %a@ and %a@ do not match@]" pp th1 pp th2)
      );
      let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
      make_ ctx hyps (Expr.app_eq ctx t v)

  let bool_eq ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<hv2>in bool_eq@ th1=%a@ th2=%a@]:"
                 pp_quoted th1 pp_quoted th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th2) with
    | None ->
      errorf (fun k->k"bool-eq should have a boolean equality as conclusion in %a"
                 pp th2)
    | Some (t, u) ->
      if Expr.equal t (concl th1) then (
        let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
        make_ ctx hyps u
      ) else (
        errorf
          (fun k->k
              "bool-eq: mismatch,@ conclusion of %a@ does not match LHS of %a@ \
               (lhs is: `@[%a@]`)"
              pp_quoted th1 pp_quoted th2 Expr.pp t)
      )

  let bool_eq_intro ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in bool_eq_intro@ th1=`@[%a@]`@ th2=`@[%a@]`@]:"
                 pp th1 pp th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let e1 = concl th1 in
    let e2 = concl th2 in
    let hyps =
      merge_hyps_
        (Expr.Set.remove e1 (hyps_ th2))
        (Expr.Set.remove e2 (hyps_ th1))
    in
    make_ ctx hyps (Expr.app_eq ctx e1 e2)

  let beta_conv ctx e : t =
    wrap_exn (fun k->k"@[<2>in beta-conv `@[%a@]`:" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.view e with
    | E_app (f, a) ->
      (match Expr.view f with
       | E_lam (_, ty_v, body) ->
         assert (Expr.equal ty_v (Expr.ty_exn a)); (* else `app` would have failed *)
         let rhs = Expr.subst_db_0 ctx body ~by:a in
         make_ ctx Expr.Set.empty (Expr.app_eq ctx e rhs)
       | _ ->
         errorf (fun k->k"not a redex: function %a is not a lambda" Expr.pp f)
      )
    | _ ->
      errorf (fun k->k"not a redex: %a not an application" Expr.pp e)

  let abs ctx v th : t =
    wrap_exn (fun k->k"@[<2>in abs :var %a `@[%a@]`:" Var.pp v pp th) @@ fun () ->
    ctx_check_th_uid ctx th;
    ctx_check_e_uid ctx v.v_ty;
    match Expr.unfold_eq th.th_concl with
    | Some (a,b) ->
      let is_in_hyp hyp = Iter.mem ~eq:Var.equal v (Expr.free_vars_iter hyp) in
      if Expr.Set.exists is_in_hyp th.th_hyps then (
        errorf (fun k->k"variable `%a` occurs in an hypothesis@ of %a" Var.pp v pp th);
      );
      make_ ctx th.th_hyps
        (Expr.app_eq ctx (Expr.lambda ctx v a) (Expr.lambda ctx v b))
    | None -> errorf (fun k->k"conclusion of `%a`@ is not an equation" pp th)

  let new_basic_definition ctx ?def_loc (e:expr) : t * const =
    Log.debugf 5 (fun k->k"(@[new-basic-def@ :eqn `%a`@])" Expr.pp e);
    wrap_exn (fun k->k"@[<2>in new-basic-def@ `@[%a@]`@]:" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.unfold_eq e with
    | None ->
      errorf (fun k->k"new-basic-def: expect an equation `x=rhs`,@ got %a" Expr.pp e)
    | Some (x, rhs) ->
      if Expr.contains rhs ~sub:x then (
        errorf (fun k->k"RHS %a@ contains variable %a" Expr.pp rhs Expr.pp x)
      );
      if not (Expr.is_closed rhs) then (
        errorf (fun k->k"RHS %a@ is not closed" Expr.pp rhs);
      );
      let x_var = match Expr.view x with
        | E_var v -> v
        | _ ->
          errorf (fun k-> k "LHS must be a variable,@ but got %a" Expr.pp x)
      in

      let fvars = Expr.free_vars rhs in
      let ty_vars_l = Var.Set.to_list fvars in
      begin match List.find (fun v -> not (Expr.is_eq_to_type v.v_ty)) ty_vars_l with
        | v ->
          errorf
            (fun k->k"RHS contains free variable `@[%a : %a@]`@ which is not a type variable"
                Var.pp v Expr.pp v.v_ty)
        | exception Not_found -> ()
      end;

      let c = Expr.new_const ctx ?def_loc (Var.name x_var) ty_vars_l (Var.ty x_var) in
      let c_e = Expr.const ctx c (List.map (Expr.var ctx) ty_vars_l) in
      let th = make_ ctx Expr.Set.empty (Expr.app_eq ctx c_e rhs) in
      th, c

  let new_basic_type_definition ctx
      ?ty_vars:provided_ty_vars
      ~name ~abs ~repr ~thm_inhabited () : New_ty_def.t =
    wrap_exn (fun k->k"@[<2>in new-basic-ty-def :name %s@ :thm `@[%a@]`@]:"
                 name pp thm_inhabited) @@ fun () ->
    ctx_check_th_uid ctx thm_inhabited;
    if has_hyps thm_inhabited then (
      errorf (fun k->k"theorem %a must not have any hypothesis" pp thm_inhabited);
    );
    let phi, witness = match Expr.view (concl thm_inhabited) with
      | E_app (phi,w) -> phi, w
      | _ ->
        errorf (fun k->k"expected conclusion of theorem %a@ to be an application"
                   pp thm_inhabited);
    in
    (* the concrete type *)
    let ty = Expr.ty_exn witness in
    (* check that all free variables in [phi] are type variables *)
    let fvars_phi = Expr.free_vars phi in
    let all_ty_fvars =
      Expr.free_vars_iter witness
      |> Iter.filter (fun v -> Expr.is_eq_to_type v.v_ty)
      |> Var.Set.add_iter fvars_phi
    in
    begin match
        Var.Set.find_first (fun v -> not (Expr.is_eq_to_type (Var.ty v))) fvars_phi
      with
      | v ->
        errorf (fun k->k"free variable %a@ occurs in Phi (in `|- Phi t`)@ \
                         and it is not a type variable" Var.pp_with_ty v)
      | exception Not_found -> ()
    end;

    let ty_vars_l = match provided_ty_vars with
      | None -> Var.Set.to_list all_ty_fvars (* pick any order *)
      | Some l ->
        if not (Var.Set.equal all_ty_fvars (Var.Set.of_list l)) then (
          errorf
            (fun k->k
                "list of type variables (%a) in new-basic-ty-def@ does not match %a"
                (Fmt.Dump.list Var.pp) (Var.Set.to_list all_ty_fvars)
                (Fmt.Dump.list Var.pp) l);
        );
        l
    in
    let ty_vars_expr_l = ty_vars_l |> CCList.map (Expr.var ctx) in

    Log.debugf 5
      (fun k->k"(@[new-basic-ty-def@ :name `%s`@ :phi %a@ \
                :ty-vars %a@ :repr `%s`@ :abs `%s`@])"
           name pp_quoted thm_inhabited (Fmt.Dump.list Var.pp) ty_vars_l repr abs);

    (* construct new type and mapping functions *)
    let tau = Expr.new_ty_const ctx name (List.length ty_vars_l) in
    let tau_vars = Expr.const ctx tau ty_vars_expr_l in

    let c_abs =
      let ty = Expr.arrow ctx ty tau_vars in
      Expr.new_const ctx abs ty_vars_l ty
    in
    let c_repr =
      let ty = Expr.arrow ctx tau_vars ty in
      Expr.new_const ctx repr ty_vars_l ty
    in

    let abs_x = Var.make "x" tau_vars in
    (* `|- abs (repr x) = x` *)
    let abs_thm =
      let abs_x = Expr.var ctx abs_x in
      let repr = Expr.const ctx c_repr ty_vars_expr_l in
      let t = Expr.app ctx repr abs_x in
      let abs = Expr.const ctx c_abs ty_vars_expr_l in
      let abs_t = Expr.app ctx abs t in
      let eqn = Expr.app_eq ctx abs_t abs_x in
      make_ ctx Expr.Set.empty eqn
    in

    let repr_x = Var.make "x" ty in
    (* `|- Phi x <=> repr (abs x) = x` *)
    let repr_thm =
      let repr_x = Expr.var ctx repr_x in
      let abs = Expr.const ctx c_abs ty_vars_expr_l in
      let t1 = Expr.app ctx abs repr_x in
      let repr = Expr.const ctx c_repr ty_vars_expr_l in
      let t2 = Expr.app ctx repr t1 in
      let eq_t2_x = Expr.app_eq ctx t2 repr_x in
      let phi_x = Expr.app ctx phi repr_x in
      make_ ctx Expr.Set.empty (Expr.app_eq ctx phi_x eq_t2_x)
    in

    {New_ty_def.
      tau; c_repr; c_abs; fvars=ty_vars_l; repr_x;
      repr_thm; abs_x; abs_thm}
end

module type THM_FOR_CTX = THM with type 'a with_ctx := 'a

let make_thm (ctx:ctx) : (module THM_FOR_CTX) =
  let module M = struct
    include Thm

    let assume = assume ctx
    let axiom = axiom ctx
    let cut = cut ctx
    let refl = refl ctx
    let congr = congr ctx
    let subst = subst ctx
    let sym = sym ctx
    let trans = trans ctx
    let bool_eq = bool_eq ctx
    let bool_eq_intro = bool_eq_intro ctx
    let beta_conv = beta_conv ctx
    let abs = abs ctx
    let new_basic_definition = new_basic_definition ctx
    let new_basic_type_definition = new_basic_type_definition ctx
  end in
  (module M)

module Theory = struct
  type t = theory

  let pp_name out self = Name.pp out self.theory_name
  let pp out (self:t) : unit =
    let {theory_name=name; theory_ctx=_; theory_in_constants=inc;
         theory_in_theorems=inth; theory_defined_theorems=dth;
         theory_defined_constants=dc; } = self in
    Fmt.fprintf out "(@[<v1>theory %a" Name.pp name;
    Str_k_map.iter (fun _ c ->
        Fmt.fprintf out "@,(@[in-const@ %a@])" Const.pp_with_ty c)
      inc;
    List.iter (fun th -> Fmt.fprintf out "@,(@[in-thm@ %a@])" Thm.pp_quoted th) inth;
    Str_k_map.iter
      (fun _ c ->
         Fmt.fprintf out "@,(@[defined-const@ %a@])" Const.pp_with_ty c)
      dc;
    List.iter (fun th -> Fmt.fprintf out "@,(@[defined-thm@ %a@])" Thm.pp_quoted th) dth;
    Fmt.fprintf out "@])";
    ()

  let to_string = Fmt.to_string pp

  let assume self hyps concl : thm =
    let ctx = self.theory_ctx in
    Thm.wrap_exn (fun k->k"in theory_assume@ `@[%a@ |- %a@]`:"
                 (pp_list Expr.pp) hyps Expr.pp concl) @@ fun () ->
    if not (Thm.is_bool_ ctx concl && List.for_all (Thm.is_bool_ ctx) hyps) then (
      error "Theory.assume: all terms must be booleans"
    );
    let hyps = Expr.Set.of_list hyps in
    {(Thm.make_ ctx hyps concl) with th_theory=Some self}

  let assume_const_ self (c:const) : unit =
    let s = (c.c_name :> string) in
    let kind = if Expr.is_eq_to_type c.c_ty then C_ty else C_term in
    if Str_k_map.mem (kind,s) self.theory_in_constants then (
      errorf (fun k->k"Theory.assume_const: constant `%s` already exists" s);
    );
    self.theory_in_constants <- Str_k_map.add (kind,s) c self.theory_in_constants;
    ()

  let assume_const = assume_const_
  let assume_ty_const = assume_const_

  let add_const_ self c : unit =
    let s = Name.to_string c.c_name in
    let kind = if Expr.is_eq_to_type c.c_ty then C_ty else C_term in
    begin match Str_k_map.get (kind,s) self.theory_defined_constants with
      | Some c' when Const.equal c c' ->
        Log.debugf 2 (fun k->k"redef `%s`" s);
      | Some _ ->
        errorf (fun k->k"Theory.add_const: constant `%s` already defined" s);
      | None -> ()
    end;
    self.theory_defined_constants <- Str_k_map.add (kind,s) c self.theory_defined_constants

  let add_const = add_const_
  let add_ty_const = add_const_

  let[@inline] find_const self s : _ option =
    try Some (Str_k_map.find (C_term,s) self.theory_defined_constants)
    with Not_found -> Str_k_map.get (C_term,s) self.theory_in_constants

  let[@inline] find_ty_const self s : _ option =
    try Some (Str_k_map.find (C_ty,s) self.theory_defined_constants)
    with Not_found -> Str_k_map.get (C_ty,s) self.theory_in_constants

  let add_theorem self th : unit =
    begin match th.th_theory with
      | None -> th.th_theory <- Some self
      | Some theory' when theory' == self -> ()
      | Some theory' ->
        errorf (fun k->k"Theory.add_theorem:@ %a@ already belongs in theory `%a`"
                   Thm.pp_quoted th Name.pp theory'.theory_name);
    end;
    self.theory_defined_theorems <- th :: self.theory_defined_theorems

  let mk_ ctx ~name : t =
    { theory_name=name; theory_ctx=ctx;
      theory_in_constants=Str_k_map.empty;
      theory_defined_constants=Str_k_map.empty;
      theory_in_theorems=[]; theory_defined_theorems=[]
    }

  let mk_str_ ctx ~name : t =
    let name = Name.make name in
    mk_ ctx ~name

  let with_ ctx ~name f : t =
    let self = mk_str_ ctx ~name in
    f self;
    self

  (* check that all theories in [l] come from context [ctx] *)
  let check_same_ctx_ ctx l =
    List.iter
      (fun th -> if th.theory_ctx != ctx
        then errorf (fun k->k"theory `%a` comes from a different context" pp_name th))
      l

  let union_const_map_ ~what m1 m2 =
    Str_k_map.union
      (fun (_,s) c1 c2 ->
         if not (Const.equal c1 c2) then (
           errorf (fun k->k"incompatible %s constant `%s`: %a vs %a"
                      what s Const.pp c1 Const.pp c2)
         );
         Some c1)
      m1 m2

  (* FIXME: update theorems' theory pointer? *)
  let union ctx ~name l : t =
    check_same_ctx_ ctx l;
    let self = mk_str_ ctx ~name in
    List.iter
      (fun th ->
        self.theory_in_constants <-
          union_const_map_ ~what:"assumed"
            self.theory_in_constants th.theory_in_constants;
        self.theory_defined_constants <-
          union_const_map_ ~what:"defined"
            self.theory_defined_constants th.theory_defined_constants;
        self.theory_in_theorems <-
          List.rev_append th.theory_in_theorems self.theory_in_theorems;
        self.theory_defined_theorems <-
          List.rev_append th.theory_defined_theorems self.theory_defined_theorems;
      )
      l;
    self

  (* interpretation: map some constants to other constants *)
  type interpretation = string Str_map.t

  let pp_interp out (i:interpretation) : unit =
    let pp_pair out (s,u) = Fmt.fprintf out "(@[`%s` =>@ `%s`@])" s u in
    Fmt.fprintf out "{@[%a@]}"
      (Fmt.iter ~sep:(Fmt.return "@ ") pp_pair) (Str_map.to_iter i)

  module Instantiate_ = struct
    type state = {
      ctx: Ctx.t;
      cache: expr Expr.Tbl.t;
      interp: interpretation;
      find_const: Name.t -> ty:Expr.t -> const option;
      (* context in which to try to reinterpret constants *)
    }

    let create
        ?(find_const=fun _ ~ty:_ -> None)
        ?(interp=Str_map.empty) ctx : state =
      { ctx; interp; cache=Expr.Tbl.create 32; find_const; }

    (* instantiate one term *)
    let rec inst_t_ (self:state) (e:expr) : expr =
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
              if Const.equal c c' && List.for_all2 Expr.equal args args'
              then e
              else Expr.const self.ctx c' args'
            | _ ->
              Expr.map self.ctx e ~f:(fun _ e' -> loop e')
          in
          Expr.Tbl.add self.cache e u;
          u
      in
      loop e

    and inst_const_ (self:state) (c:const) : const =
      let ty' = inst_t_ self c.c_ty in
      let name' =
        try Name.make (Str_map.find (c.c_name :> string) self.interp)
        with Not_found -> c.c_name
      in
      (* reinterpret constant? *)
      begin match self.find_const name' ~ty:ty' with
        | Some c' when Expr.is_eq_to_type c'.c_ty -> c'
        | Some c' ->
          (* reintepret into [c']… whose type might also change *)
          let ty'' = inst_t_ self c'.c_ty in
          Const.make_ self.ctx {c' with c_ty=ty''}
        | None ->
          Const.make_ self.ctx {c with c_name=name'; c_ty=ty'}
      end

    let inst_constants_ (self:state) (m:const Str_k_map.t) : _ Str_k_map.t =
      Str_k_map.to_iter m
      |> Iter.map
        (fun ((k,_),c) ->
           let c' = inst_const_ self c in
           (k,(c'.c_name :> string)), c')
      |> Str_k_map.of_iter

    (* instantiate a whole theorem *)
    let inst_thm_ (self:state) (th:thm) : thm =
      let hyps =
        Expr.Set.to_iter th.th_hyps
        |> Iter.map (inst_t_ self)
        |> Expr.Set.of_iter
      in
      let concl = inst_t_ self th.th_concl in
      Thm.make_ self.ctx hyps concl

    let inst_theory_ (self:state) (th:theory) : theory =
      assert (self.ctx == th.theory_ctx);
      let {
        theory_ctx=_; theory_name; theory_in_constants;
        theory_in_theorems; theory_defined_constants;
        theory_defined_theorems} = th in
      let th' = mk_ self.ctx ~name:theory_name in
      th'.theory_in_constants <-
        inst_constants_ self theory_in_constants;
      th'.theory_defined_constants <-
        inst_constants_ self theory_defined_constants;
      th'.theory_in_theorems <-
        List.map (inst_thm_ self) theory_in_theorems;
      th'.theory_defined_theorems <-
        List.map (inst_thm_ self) theory_defined_theorems;
      th'
  end

  let instantiate ~(interp:interpretation) th : t =
    if Str_map.is_empty interp then th
    else (
      let st = Instantiate_.create ~interp th.theory_ctx in
      Instantiate_.inst_theory_ st th
    )

  (* index by name+ty, for constants *)
  module Name_ty_tbl = CCHashtbl.Make(struct
      type t = Name.t * Expr.t
      let equal (n1,ty1) (n2,ty2) = Name.equal n1 n2 && Expr.equal ty1 ty2
      let hash (n,ty) = H.(combine3 25 (Name.hash n) (Expr.hash ty))
    end)

  (* index theorems by [hyps |- concl] *)
  module Thm_tbl = CCHashtbl.Make(struct
      type t = thm
      let equal th1 th2 =
        Expr.equal th1.th_concl th2.th_concl &&
        Expr.Set.equal th1.th_hyps th2.th_hyps
      let hash th =
        H.(combine3 192 (Expr.hash th.th_concl)
             (iter Expr.hash (Expr.Set.to_iter th.th_hyps)))
    end)

  let compose ?(interp=Str_map.empty) l th : t =
    Log.debugf 2
      (fun k->k"(@[theory.compose@ %a@ %a@ @[:interp %a@]@])"
          Fmt.(Dump.list pp_name) l pp_name th pp_interp interp);

    if CCList.is_empty l then (
      instantiate ~interp th
    ) else (
      let ctx = th.theory_ctx in

      (* reinterpret constants that are provided by [l]. For that we need
         to index them by [name,ty].
         Also gather the set of proved theorems from *)
      let const_tbl_ = Name_ty_tbl.create 32 in
      let provided_thms = Thm_tbl.create 32 in

      List.iter
        (fun th0 ->
           Str_k_map.iter (fun _ c -> Name_ty_tbl.replace const_tbl_ (c.c_name,c.c_ty) c)
             th0.theory_in_constants;
           Str_k_map.iter (fun _ c -> Name_ty_tbl.replace const_tbl_ (c.c_name,c.c_ty) c)
             th0.theory_defined_constants;
           List.iter (fun th -> Thm_tbl.replace provided_thms th ())
             th0.theory_defined_theorems;
        )
        l;

      let find_const name ~ty = Name_ty_tbl.get const_tbl_ (name,ty) in

      let st = Instantiate_.create ~find_const ~interp ctx in
      let th = Instantiate_.inst_theory_ st th in

      (* remove provided constants *)
      th.theory_in_constants <-
        Str_k_map.filter
          (fun _ c ->
            not (Name_ty_tbl.mem const_tbl_ (c.c_name,c.c_ty)))
          th.theory_in_constants;
      (* remove satisfied assumptions *)
      th.theory_in_theorems <-
        CCList.filter
          (fun th -> not (Thm_tbl.mem provided_thms th))
          th.theory_in_theorems;
      (* add assumptions from [l] *)
      th.theory_in_theorems <-
        List.fold_left
          (fun l th' -> List.rev_append th'.theory_in_theorems l)
          th.theory_in_theorems l;

      th
    )
end

(* ok def *)
(*$R
  let a_ = v' "a" type_ in
  let ok_def, _thm =
    Thm.new_basic_definition ctx
      (let thevar = v (v' "body" (v a_ @-> v a_)) in
       let x = v' "x" (v a_) in
       eq thevar (lambda x (v x)))
  in
  ()
*)

