module K = Trustee_core.Kernel

type view = ..

type ops = {
  op_pp : view Fmt.printer;
  op_equal : view -> view -> bool;
  op_hash : view -> int;
}

type t = {
  view: view;
  ops: ops;
}
type value = t

let[@inline] equal a b = a.ops.op_equal a.view b.view
let[@inline] hash a = a.ops.op_hash a.view
let[@inline] pp out a = a.ops.op_pp out a.view

module type SPECIALIZED = sig
  type concrete
  type nonrec t = private t

  val make : concrete -> t
  val get : t -> concrete
  val cast : value -> concrete option
end

let make_specialized
    (type a)
    ~pp ~equal ~hash
    () : (module SPECIALIZED with type concrete=a) =
  let module S = struct
    type concrete = a
    type nonrec t = t
    type view += View of concrete

    (* here we just ignore impossible cases *)
    [@@@ocaml.warning "-w-8"]

    let ops = {
      op_pp=(fun out (View b) -> pp out b);
      op_equal=(fun (View a) b ->
          match b with View b -> equal a b | _ -> false);
      op_hash=(fun (View v) -> hash v);
    }

    let[@inline] make x = {view=View x; ops}
    let[@inline] get {view=View x;_} = x

    [@@@ocaml.warning "-w+8"]

    let[@inline] cast = function
      | {view=View x;_} -> Some x
      | _ -> None
  end in
  (module S)

(* TODO: use a sum type for the common cases below, use extensibility for
   more exotic cases *)

module Bool =
  (val make_specialized ~pp:Fmt.bool ~equal:Stdlib.(=) ~hash:CCHash.bool ())

module Int =
  (val make_specialized
      ~pp:Fmt.int ~equal:Stdlib.(=) ~hash:CCHash.int ())

module Expr =
  (val make_specialized
      ~pp:K.Expr.pp ~equal:K.Expr.equal ~hash:K.Expr.hash ())

module Thm =
  (val make_specialized
      ~pp:K.Thm.pp ~equal:K.Thm.equal ~hash:K.Thm.hash ())

module Subst =
  (val make_specialized
      ~pp:K.Subst.pp ~equal:K.Subst.equal ~hash:K.Subst.hash ())
