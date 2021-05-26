
open Sigs
module K = Kernel
module E = K.Expr

module Vec = CCVector

type node = {
  e: E.t;
  mutable next: node; (* next element in the class *)
  mutable root: node; (* pointer to representative *)
  mutable expl: (node * expl) option; (* proof forest *)
  mutable parents: node list;
  sigt: signature option;
}

and signature =
  | S_app of node * node

and expl =
  | Exp_cong
  | Exp_merge of K.thm
  (* merge [a] and [b] because of theorem [… |- a=b], modulo commutativity *)

type merge_task = Merge of node * node * expl
type update_sig_task = Update_sig of node [@@unboxed]

(* signature table *)
module Sig_tbl = CCHashtbl.Make(struct
    type t = signature
    let equal s1 s2 = match s1, s2 with
      | S_app (x1,y1), S_app (x2,y2) ->
        x1==x2 && y1==y2
    let hash = function
      | S_app (a,b) -> CCHash.(combine3 28 (E.hash a.e) (E.hash b.e))
  end)

(* congruence closure state *)
type t = {
  ctx: K.ctx;
  nodes: node E.Tbl.t;
  to_merge: merge_task Vec.vector;
  to_update_sig: update_sig_task Vec.vector;
  sigs: node Sig_tbl.t;
  tmp_tbl: unit E.Tbl.t;
}

let create ctx : t =
  { ctx;
    nodes=E.Tbl.create 32;
    to_merge=Vec.create();
    to_update_sig=Vec.create();
    sigs=Sig_tbl.create 16;
    tmp_tbl=E.Tbl.create 16;
  }

let[@inline] res_thm_eq_ (th:K.thm) : E.t * E.t =
  match E.unfold_eq (K.Thm.concl th) with
  | Some (a,b) -> a, b
  | None ->
    errorf (fun k->k"theorem %a should be an equation" K.Thm.pp_quoted th)

(* find representative of the class *)
let[@unroll 2] rec find (n:node) : node =
  if n.root == n then n
  else (
    let root = find n.root in
    n.root <- root;
    root
  )

(* nodes are equal? *)
let[@inline] are_eq (n1:node) (n2:node) : bool =
  find n1 == find n2

(* find common ancestor of nodes. Precondition: [are_eq n1 n2] *)
let find_common_ancestor (self:t) (n1:node) (n2:node) : node =
  let tbl = self.tmp_tbl in

  let rec add_path1 n =
    E.Tbl.add tbl n.e ();
    match n.expl with
    | None -> ()
    | Some (n2,_expl) -> add_path1 n2
  in
  add_path1 n1;

  let rec find n =
    if E.Tbl.mem tbl n.e then n
    else match n.expl with
      | None -> assert false
      | Some (n2,_) -> find n2
  in

  let res = find n2 in
  E.Tbl.reset tbl; (* be sure to reset *)
  res

let rec prove_eq (self:t) (n1:node) (n2:node) : K.thm =
  if n1 == n2 then (
    K.Thm.refl self.ctx n1.e
  ) else (
    let n = find_common_ancestor self n1 n2 in
    let th1 = explain_along_ self n1 n in
    let th2 = explain_along_ self n2 n in
    (* th1: [|- n1=n], th2: [|- n2=n], so build [|- n1=n2] via
       transivity of th1 and sym(th2)==[|- n=n2] *)
    let th = K.Thm.trans self.ctx th1 (K.Thm.sym self.ctx th2) in
    th
  )

(* explain why [n0 = parent].
   Precondition: parent is in the chain of explanation of [n0]. *)
and explain_along_ (self:t) (n0:node) (parent:node) : K.Thm.t =
  (* invariant: th is [|- n0=n1] *)
  let rec loop th n1 =
    if n1==parent then th
    else (
      match n1.expl with
      | None -> assert false
      | Some (n2, e_1_2) ->
        (* get a proof of [|- n1.e = n2.e] *)
        let th_12 =
          match e_1_2 with
          | Exp_merge th_12 ->
            let x,y = res_thm_eq_ th_12 in
            if x == n1.e then (
              assert (y==n2.e);
              th_12
            ) else (
              assert (x==n2.e && y==n1.e);
              K.Thm.sym self.ctx th_12
            )
          | Exp_cong ->
            match n1.sigt, n2.sigt with
            | Some (S_app (a1,b1)), Some (S_app (a2,b2)) ->
              let th_sub_1 = prove_eq self a1 a2 in
              let th_sub_2 = prove_eq self b1 b2 in
              K.Thm.congr self.ctx th_sub_1 th_sub_2
            | None, _ | _, None -> assert false
        in
        (* now prove [|- n0.e = n2.e] *)
        let th' = K.Thm.trans self.ctx th th_12 in
        loop th' n2
    )
  in
  loop (K.Thm.refl self.ctx n0.e) n0

let rec add_ (self:t) (e:E.t) : node =
  try E.Tbl.find self.nodes e
  with Not_found ->
    add_uncached_ self e

and add_uncached_ self e =
  let sigt, subs = match E.view e with
    | E.E_app (f, x) ->
      let n_f = find @@ add_ self f in
      let n_x = find @@ add_ self x in
      Some (S_app (n_f, n_x)), [n_f; n_x]
    | _ -> None, []
  in
  let rec node = {
    e; sigt; next=node; root=node; expl=None; parents=[];
  } in
  E.Tbl.add self.nodes e node;
  List.iter (fun sub -> sub.parents <- node :: sub.parents) subs;
  if CCOpt.is_some sigt then (
    Vec.push self.to_update_sig (Update_sig node)
  );
  node

let[@inline] canon_sig (s:signature) : signature =
  match s with
  | S_app (n1, n2) -> S_app (find n1, find n2)

(* iterate on all nodes in the class of [n0] *)
let iter_class_ (n0:node) f : unit =
  let continue = ref true in
  let n = ref n0 in
  while !continue do
    f !n;
    n := (!n).next;
    if !n == n0 then continue := false
  done

(* make sure [n1] is the root of its proof forest *)
let[@unroll 2] rec reroot_at (n1:node) : unit =
  match n1.expl with
  | None -> ()
  | Some (n2, e_12) ->
    reroot_at n2;
    assert (n2.expl == None);
    n2.expl <- Some (n1, e_12);
    ()

(* main repair loop *)
let update (self:t) : unit =
  while not (Vec.is_empty self.to_merge && Vec.is_empty self.to_update_sig) do
    Vec.iter
      (fun (Merge (n1,n2,e_12)) ->
         let r1 = find n1 in
         let r2 = find n2 in
         if r1 != r2 then (
           (* merge r1 into r2 *)
           iter_class_ r1
             (fun n1' ->
                n1'.root <- r2;
                (* update signature of [parents(n1')] *)
                List.iter
                  (fun n1'_p -> Vec.push self.to_update_sig (Update_sig n1'_p))
                  n1'.parents);
           (* add explanation for the merge *)
           reroot_at n1;
           assert (n1.expl == None);
           n1.expl <- Some (n2, e_12);
         ))
      self.to_merge;
    Vec.clear self.to_merge;

    Vec.iter
      (fun (Update_sig n) ->
         begin match n.sigt with
           | None -> ()
           | Some s ->
             let s' = canon_sig s in
             match Sig_tbl.get self.sigs s' with
             | None -> Sig_tbl.add self.sigs s' n
             | Some n' when are_eq n n' -> ()
             | Some n' -> Vec.push self.to_merge (Merge (n,n',Exp_cong))
         end)
      self.to_update_sig;
    Vec.clear self.to_update_sig;
  done;
  ()

let add_thm (self:t) (th:K.thm) : unit =
  match E.unfold_eq (K.Thm.concl th) with
  | Some (a,b) ->
    let a = add_ self a in
    let b = add_ self b in
    Vec.push self.to_merge (Merge (a,b,Exp_merge th));
  | None ->
    errorf (fun k->k"cannot add non-equational theorem %a" K.Thm.pp_quoted th)

let prove_cc (ctx:K.ctx) (hyps:K.thm list) (t:E.t) (u:E.t) : _ option =
  let self = create ctx in
  List.iter (add_thm self) hyps;
  let n_t = add_ self t in
  let n_u = add_ self u in

  update self;
  if find n_t == find n_u then (
    let th = prove_eq self n_t n_u in
    Some th
  ) else (
    None
  )
