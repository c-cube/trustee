
module Make(C : Core.S) = struct
  open C.KoT

  module T = Expr

  let x = T.new_var "x" T.bool

  (* [true = ((λx.x)=(λx.x))] *)
  let true_def, true_ =
    Thm.new_basic_definition
      (T.eq
         (T.new_var' "true" T.bool)
         (T.eq (T.lambda x (T.var x)) (T.lambda x (T.var x))))

  let true_is_true =
    let th_true = Thm.abs x (Thm.refl (T.var x)) in
    Thm.bool_eq ~eq:(C.sym true_def) th_true

  (* [false = (λx. T)=(λx. x)] *)
  let false_def, false_ =
    Thm.new_basic_definition
      (T.eq
         (T.new_var' "false" T.bool)
         (T.eq (T.lambda x true_) (T.lambda x (T.var x))))

  let true_eq_intro th : Thm.t =
    (* from [F |- t], and [|- true] (obtained with [abs x (refl x)]),
       deduce [F |- t=true] by [eq_bool_intro] *)
    Thm.bool_eq_intro th true_is_true

  let true_eq_elim th : Thm.t =
    try
      (* from [F |- t=true] get [F |- true=t] by sym, then
         bool_eq with [|- true]. *)
      let th = C.sym th in
      Thm.bool_eq ~eq:th true_is_true
    with Error msg ->
      error_wrapf_ msg (fun k->k "([@in true_eq_elim@ %a@])" Thm.pp th)

  (* TODO: prove [F |- t=true] --> [F |- t] *)
  (* TODO: prove [F |- t] --> [F |- t=true] *)
  (* TODO: prove [F, true |- t] --> [F |- t] *)

  let and_const : T.t = T.new_const_infix "/\\" T.(bool @-> bool @-> bool)
  let or_const : T.t = T.new_const_infix "\\/" T.(bool @-> bool @-> bool)
  let not_const : T.t = T.new_const "~" T.(bool @-> bool)

  let and_ a b : T.t = T.app_l and_const [a;b]
  let or_ a b : T.t = T.app_l or_const [a;b]
  let not_ a : T.t = T.app not_const a
  let rec and_l = function [] -> true_ | [t] -> t | t :: ts -> and_ t (and_l ts)
  let rec or_l = function [] -> false_ | [t] -> t | t :: ts -> or_ t (or_l ts)

  (* TODO: basic theorems for manipulating formulas *)
  (* TODO: quantifiers *)
  (* TODO: rules to manipulate booleans *)
end
