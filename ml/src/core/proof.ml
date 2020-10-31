
open Sigs
module K = Kernel

module Rule = struct
  type arg_ty =
    | Arg_expr
    | Arg_thm
    | Arg_subst

  type arg_val =
    | AV_expr of K.Expr.t
    | AV_thm of K.Thm.t
    | AV_subst of K.Subst.t

  type signature = arg_ty list

  type t = {
    r_name: string;
    r_args: arg_ty list;
    r_view: view;
  }

  and view =
    | R_native of {
        run: K.Ctx.t -> arg_val list -> K.Thm.t
      }
    | R_defined of defined_rule

  and defined_rule = unit (* TODO *)
  (** A defined rule *)

  let[@inline] signature r = r.r_args

  let pp out (r:t) : unit = Fmt.string out r.r_name
  let to_string = Fmt.to_string pp

  let string_of_arg = function
    | Arg_thm -> "thm"
    | Arg_subst -> "subst"
    | Arg_expr -> "expr"
  let pp_arg_ty out a = Fmt.string out (string_of_arg a)

  let pp_arg_val out v =
    match v with
    | AV_expr e -> K.Expr.pp out e
    | AV_thm th -> K.Thm.pp out th
    | AV_subst s -> K.Subst.pp out s

  let pp_signature = Fmt.Dump.list pp_arg_ty

  (* ### define builtins ### *)

  let err_badarg what i v =
    errorf
      (fun k->k"expected %d-th arg@ to be %s,@ not %a"
          i what pp_arg_val v)
  let as_e i = function
    | AV_expr e -> e
    | v -> err_badarg "an expression" i v
  and as_th i = function
    | AV_thm e -> e
    | v -> err_badarg "a theorem" i v
  and as_subst i = function
    | AV_subst s -> s
    | v -> err_badarg "a substitution" i v

  let mk_ r_name r_view r_args : t =
    { r_name; r_view; r_args; }

  let mk_native_ name args run : t =
    mk_ name (R_native {run}) args

  let assume : t =
    mk_native_ "assume" [Arg_expr] @@
    fun ctx args -> match args with
    | [v] ->
      let e = as_e 0 v in
      K.Thm.assume ctx e
    | _ -> assert false

  let cut : t =
    mk_native_ "cut" [Arg_thm; Arg_thm] @@
    fun ctx args -> match args with
    | [v1;v2] ->
      let th1 = as_th 0 v1 in
      let th2 = as_th 0 v2 in
      K.Thm.cut ctx th1 th2
    | _ -> assert false

  let refl : t =
    mk_native_ "refl" [Arg_expr] @@
    fun ctx args -> match args with
    | [v1] ->
      let e = as_e 0 v1 in
      K.Thm.refl ctx e
    | _ -> assert false

  let congr : t =
    mk_native_ "congr" [Arg_thm; Arg_thm] @@
    fun ctx args -> match args with
    | [v1;v2] ->
      let th1 = as_th 0 v1 in
      let th2 = as_th 0 v2 in
      K.Thm.congr ctx th1 th2
    | _ -> assert false

  let congr_ty : t =
    mk_native_ "congr_ty" [Arg_thm; Arg_expr] @@
    fun ctx args -> match args with
    | [v1;v2] ->
      let th1 = as_th 0 v1 in
      let e2 = as_e 0 v2 in
      K.Thm.congr_ty ctx th1 e2
    | _ -> assert false

  let subst : t =
    mk_native_ "subst" [Arg_thm; Arg_subst] @@
    fun ctx args -> match args with
    | [v1;v2] ->
      let th1 = as_th 0 v1 in
      let s2 = as_subst 0 v2 in
      K.Thm.subst ctx th1 s2
    | _ -> assert false

  let sym : t =
    mk_native_ "sym" [Arg_thm] @@
    fun ctx args -> match args with
    | [v1] ->
      let th1 = as_th 0 v1 in
      K.Thm.sym ctx th1
    | _ -> assert false

  let bool_eq : t =
    mk_native_ "bool_eq" [Arg_thm; Arg_thm] @@
    fun ctx args -> match args with
    | [v1;v2] ->
      let th1 = as_th 0 v1 in
      let th2 = as_th 0 v2 in
      K.Thm.bool_eq ctx th1 th2
    | _ -> assert false

  let bool_eq_intro : t =
    mk_native_ "bool_eq_intro" [Arg_thm; Arg_thm] @@
    fun ctx args -> match args with
    | [v1;v2] ->
      let th1 = as_th 0 v1 in
      let th2 = as_th 0 v2 in
      K.Thm.bool_eq_intro ctx th1 th2
    | _ -> assert false

  let beta_conv : t =
    mk_native_ "beta_conv" [Arg_expr] @@
    fun ctx args -> match args with
    | [v1] ->
      let e1 = as_e 0 v1 in
      K.Thm.beta_conv ctx e1
    | _ -> assert false

  let apply ctx (r:t) args : K.Thm.t =
    let n_args = List.length args in
    let n_r_args = List.length r.r_args in
    if n_args <> n_r_args then (
      errorf (fun k->k"rule %s expected %d arguments@ but is given %d"
                 r.r_name n_r_args n_args);
    );
    begin match r.r_view with
      | R_native {run} ->
        begin
          try run ctx args
          with e ->
            errorf ~src:e (fun k->k"while applying rule %s" r.r_name)
        end
      | R_defined _ -> assert false (* TODO *)
    end

  (* list of pre-defined builtins *)
  let builtins : t list = [
    assume; cut; refl; congr; sym; congr_ty; subst;
    bool_eq; bool_eq_intro; beta_conv;
  ]
  let find_builtin s =
    try Some (List.find (fun r -> String.equal r.r_name s) builtins)
    with Not_found -> None
end

module Defined_rule = struct
  type nonrec t = Rule.t

  (* TODO: definition of the body.
  type register = int (** A virtual register *)

  type instr = {
    ret: register;
    op: instr_op;
  }
  and instr_op =
    | I_subst of register * register
    | I_apply of register * t * register list
  type body = instr_op list

  val mk_defined :
    name:string ->
    args:arg list ->
    body:instr list ->
    unit -> t
  *)
end
