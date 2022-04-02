
open Common_

(** Abstract view of expressions *)
type ('t, 'ty) view =
  | Var of string
  | Bound_var_db of int
  | App of 't * 't
  | Const of string * 'ty list
  | Lambda of string * 'ty * 't
  | Lambda_db of string option * 'ty * 't
  | Box of 't list * 't

module type EXPR = sig
  type ty
  type t

  val pp_ty : Notation.t -> ty Fmt.printer

  val view : t -> (t, ty) view
end


module type S = sig
  module E : EXPR

  val pp : Notation.t -> E.t Fmt.printer
end

module Make(E : EXPR)
  : S with module E = E
= struct
  module E = E

  let unfold_app e =
    let rec loop acc e =
      match E.view e with
      | App (f, a) -> loop (a::acc) f
      | _ -> e, acc
    in loop [] e

  (* TODO: improve printer *)
  let pp (notation:Notation.t) out (e:E.t) : unit =
    (* @param p current precedence
       @param k depth of DB indices
       @param names optional name for each DB index (len: k)
    *)
    let rec pp_rec_ (p:Fixity.precedence) k names out e : unit =
      let pp_ty = E.pp_ty notation in
      let pp' p' out e =
        wrap_ p p' out @@ fun p -> pp_rec_ p k names out e
      in
      match E.view e with
      | Var v -> Fmt.string out v
      (* | E_var v -> Fmt.fprintf out "(@[%s : %a@])" v.v_name pp v.v_ty *)
      | Bound_var_db idx ->
        begin match CCList.nth_opt names idx with
          | Some (Some n) when n<>"" ->
            Fmt.string out n (* use name from the corresponding binder *)
          | _ ->
            if idx<k then Fmt.fprintf out "x_%d" (k-idx-1)
            else Fmt.fprintf out "%%db_%d" (idx-k)
        end
      | Const (c,[]) -> Fmt.string out c
      | Const (c,args) ->
        Fmt.fprintf out "(@[%a@ %a@])" Fmt.string c (pp_list pp_ty) args
      | App _ ->
        let f, args = unfold_app e in
        let default() =
          Fmt.fprintf out "@[%a@ %a@]" (pp' (p+1)) f (pp_list (pp' (p+1))) args
        in
        begin match E.view f, args with
          | Const (c, [_]), [a;b] when c = "=" ->
            Fmt.fprintf out "@[%a@ = %a@]" (pp' 16) a (pp' 16) b
          | Const (c,_), _::_ ->
            begin match Notation.find_name notation c, args with
              | Some (Fixity.F_infix p'), [a;b] ->
                (* regular infix *)
                wrap_ p p' out @@ fun p ->
                Fmt.fprintf out "@[%a@ %a %a@]" (pp' p) a Fmt.string c (pp' p) b

              | Some (Fixity.F_binder p'), [arg] ->
                begin match E.view arg with
                  | Lambda (v, ty, bod) ->
                    (* [binder (\v. bod)] is printed as [binder v. bod] *)
                    wrap_ p p' out @@ fun p ->
                    Fmt.fprintf out "@[%a %s:@[%a@].@ %a@]"
                      Fmt.string c v pp_ty ty
                      (pp_rec_ p k names) bod

                  | Lambda_db (None, ty, bod) ->
                    wrap_ p p' out @@ fun p ->
                    Fmt.fprintf out "(@[%a x_%d:@[%a@].@ %a@])" Fmt.string c k pp_ty ty
                      (pp_rec_ p (k+1) (None::names)) bod

                  | Lambda_db (Some v, ty, bod) ->
                    wrap_ p p' out @@ fun p ->
                    Fmt.fprintf out "(@[%a %s:@[%a@].@ %a@])" Fmt.string c v pp_ty ty
                      (pp_rec_ p (k+1) (Some v::names)) bod

                  | _ -> default()
                end

              | Some (Fixity.F_left_assoc p'), [a; b] ->
                wrap_ p p' out @@ fun p ->
                Fmt.fprintf out "@[%a@ %a %a@]" (pp' (p+1)) a Fmt.string c (pp' p) b

              | Some (Fixity.F_right_assoc p'), [a; b] ->
                wrap_ p p' out @@ fun p ->
                Fmt.fprintf out "@[%a@ %a %a@]" (pp' p) a Fmt.string c (pp' (p+1)) b

              | Some (Fixity.F_postfix p'), [arg] ->
                wrap_ p p' out @@ fun p ->
                Fmt.fprintf out "@[%a@ %a@]" (pp' p) arg Fmt.string c

              (* FIXME: handle infixr, infixl, binder *)

              | _, _ -> default()
            end
          | _ -> default()
        end
      | Lambda (v, ty, bod) ->
        (* not a DB binder *)
        Fmt.fprintf out "(@[\\%a:@[%a@].@ %a@])" Fmt.string v pp_ty ty
          (pp_rec_ 0 k names) bod
      | Lambda_db (None, ty, bod) ->
        Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp_ty ty
          (pp_rec_ 0 (k+1) (None::names)) bod
      | Lambda_db (Some v, ty, bod) ->
        Fmt.fprintf out "(@[\\%a:@[%a@].@ %a@])" Fmt.string v pp_ty ty
          (pp_rec_ 0 (k+1) (Some v::names)) bod
      | Box ([],c) ->
        Fmt.fprintf out "@[|- %a@]" (pp_rec_ 0 k names) c
      | Box (hyps,c) ->
        Fmt.fprintf out "@[<hv>%a@ |- %a@]"
          (pp_list @@ pp_rec_ 0 k names) hyps
          (pp_rec_ 0 k names) c

    (* wrap in () if [p>p']; call [k (max p p')] to print the expr *)
    and wrap_ p p' out k =
      if p>=p' then (
        Fmt.fprintf out "(@[";
        k p;
        Fmt.fprintf out "@])";
      ) else k p'
    in
    pp_rec_ 0 0 [] out e
end

module Pp_k_expr
  : S with type E.t = Trustee_core.Kernel.Expr.t
  = Make(struct
    module K = Trustee_core.Kernel
    module E = K.Expr

    type t = E.t
    type ty = E.t

    let pp_ty _notation = E.pp

    let view e = match E.view e with
      | E.E_var v -> Var (K.Var.to_string v)
      | E.E_app (f, a) -> App (f, a)
      | E.E_const (c, args) -> Const (K.Const.name c, args)
      | E.E_bound_var bv -> Bound_var_db bv.bv_idx
      | E.E_lam (s, ty, bod) ->
        let name = if s="" then None else Some s in
        Lambda_db (name, ty, bod)
      | E.E_box seq ->
        Box (K.Sequent.hyps_l seq, K.Sequent.concl seq)
      | E.E_kind | E.E_type | E.E_arrow _ -> assert false
  end)
