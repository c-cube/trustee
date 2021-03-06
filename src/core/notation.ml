
open Sigs
module K = Kernel
module N = K.Name

type fixity = Fixity.t
type t = {
  fixs: fixity Str_map.t;
} [@@unboxed]


let[@inline] find self s = Str_map.get s self.fixs
let[@inline] find_name self s = find self (N.to_string s)
let[@inline] find_or_default self s = Str_map.get_or s self.fixs ~default:Fixity.normal
let[@inline] find_name_or_default self s = find_or_default self (N.to_string s)
let[@inline] declare s f self = {fixs=Str_map.add s f self.fixs}

let empty = {fixs=Str_map.empty}

let pp out (self:t) : unit =
  let pppair out (s,f) = Fmt.fprintf out "(@[%s %a@])" s Fixity.pp f in
  Fmt.fprintf out "(@[notations@ (@[%a@])@])"
    Fmt.(iter pppair) (Str_map.to_iter self.fixs)

module Ref = struct
  type notation = t
  type nonrec t = notation ref
  let create() = ref empty
  let of_notation n = ref n
  let find self s = find !self s
  let find_or_default self s = find_or_default !self s
  let declare self s f = self := declare s f !self
  let pp out self = pp out !self
end


let empty_hol =
  empty
  |> declare "=" (Fixity.infix 18)
  |> declare "select" (Fixity.binder 10)
  |> declare "==>" (Fixity.binder 12)

(* TODO: improve printer *)
let pp_expr (not:t) out (e:K.Expr.t) : unit =
  let module E = K.Expr in
  (* @param p current precedence
     @param k depth of DB indices
     @param names optional name for each DB index
  *)
  let rec loop p k names out e : unit =
    let pp = loop p k names in
    let pp0 = loop 0 k names in
    let pp' p' out e =
      wrap_ p p' out @@ fun p -> loop p k names out e
    in
    match E.view e with
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
    | E_const (c,[]) -> N.pp out (K.Const.name c)
    | E_const (c,args) ->
      Fmt.fprintf out "(@[%a@ %a@])" K.Name.pp (K.Const.name c) (pp_list (pp' 1)) args
    | E_app _ ->
      let f, args = E.unfold_app e in
      let default() =
        Fmt.fprintf out "@[%a@ %a@]" (pp' (p+1)) f (pp_list (pp' (p+1))) args
      in

      begin match E.view f, args with
        | E_const (c, [_]), [a;b] when K.Name.equal_str (K.Const.name c) "=" ->
          Fmt.fprintf out "@[%a@ = %a@]" (pp' 16) a (pp' 16) b
        | E_const (c,_), _::_ ->
          begin match find_name not (K.Const.name c), args with
            | Some (Fixity.F_infix p'), [a;b] ->
              wrap_ p p' out @@ fun p ->
              Fmt.fprintf out "@[%a@ %a %a@]" (pp' p) a N.pp (K.Const.name c) (pp' p) b
            | _ -> default()
          end
        | _ -> default()
      end
    | E_lam ("", _ty, bod) ->
      Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp0 _ty
        (loop 0 (k+1) (""::names)) bod
    | E_lam (n, _ty, bod) ->
      Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" n pp0 _ty
        (loop 0 (k+1) (n::names)) bod
    | E_arrow(a,b) ->
      Fmt.fprintf out "@[%a@ -> %a@]" (pp' (p+1)) a pp b
  (* wrap in () if [p>p']; call [k (max p p')] to print the expr *)
  and wrap_ p p' out k =
    if p>=p' then (
      Fmt.fprintf out "(@[";
      k p;
      Fmt.fprintf out "@])";
    ) else k p'
  in
  loop 0 0 [] out e

