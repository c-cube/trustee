module K = Trustee_core.Kernel

type t = {
  consts: K.Const.t list;
  axioms: K.Thm.t list;
  theorems: K.Thm.t list;
}

val empty : t

include PP with type t := t

type item =
  | I_cst of K.Const.t
  | I_axiom of K.Thm.t
  | I_thm of K.Thm.t

val items : t -> item Iter.t

val pp_stats : t Fmt.printer
