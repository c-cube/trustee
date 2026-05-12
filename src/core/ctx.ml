open Types
open Sigs

type t = ctx

let uid_ = ref 0
let lru_size_ = try int_of_string "LRU_SIZE" with _ -> 128

let create ?(def_cache_size = lru_size_) ?(storage = Storage.in_memory ())
    ?(store_proofs = false) ?(store_concrete_definitions = false) () : t =
  let ctx_uid = !uid_ land ctx_id_mask in
  incr uid_;
  let rec ctx =
    {
      ctx_uid;
      ctx_store_concrete_definitions = store_concrete_definitions;
      ctx_store_proofs = store_proofs;
      ctx_storage = storage;
      ctx_exprs = Expr_hashcons.create ~size:2_048 ();
      ctx_axioms = [];
      ctx_axioms_allowed = true;
      ctx_def_cache = String_LRU.create ~size:def_cache_size ();
      ctx_kind = lazy (Expr.make_ ctx E_kind Kind);
      ctx_type =
        lazy
          (let kind = Expr.kind ctx in
           Expr.make_ ctx E_type (Ty kind));
      ctx_bool_c =
        lazy
          (let typ = Expr.type_ ctx in
           let c =
             Const.make ctx id_bool ~def:(C_def_magic id_bool) (C_arity 0) typ
           in
           assert (String.equal c.c_name Const.cname_bool);
           c);
      ctx_bool = lazy (Expr.const ctx (Lazy.force ctx.ctx_bool_c) []);
      ctx_eq_c =
        lazy
          (let type_ = Expr.type_ ctx in
           let a_ = Var.make "a" type_ in
           let ea = Expr.var ctx a_ in
           let typ = Expr.(arrow ctx ea @@ arrow ctx ea @@ bool ctx) in
           let c =
             Const.make ctx id_eq ~def:(C_def_magic id_eq) (C_ty_vars [ a_ ])
               typ
           in
           assert (String.equal c.c_name Const.cname_eq);
           c);
      ctx_select_c =
        lazy
          (let type_ = Expr.type_ ctx in
           let (lazy bool_) = ctx.ctx_bool in
           let a_ = Var.make "a" type_ in
           let ea = Expr.var ctx a_ in
           let typ = Expr.(arrow ctx (arrow ctx ea bool_) ea) in
           let c =
             Const.make ctx id_select ~def:(C_def_magic id_select)
               (C_ty_vars [ a_ ]) typ
           in
           assert (String.equal c.c_name Const.cname_select);
           c);
    }
  in
  ctx

let n_exprs self = Expr_hashcons.size self.ctx_exprs

let pledge_no_more_axioms self =
  if self.ctx_axioms_allowed then (
    Log.debugf 5 (fun k -> k "pledge no more axioms");
    self.ctx_axioms_allowed <- false
  )

let axioms self k = List.iter k self.ctx_axioms

let new_skolem_const self name tyvars ty : const =
  Const.make self ~def:(C_def_skolem { name }) name (C_ty_vars tyvars) ty

let new_skolem_ty_const self name ~arity : const =
  let ty = Expr.type_ self in
  Const.make self
    ~def:(C_def_skolem_ty { name; arity })
    name (C_arity arity) ty
