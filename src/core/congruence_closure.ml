
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
    Error.failf (fun k->k"theorem %a should be an equation" K.Thm.pp_quoted th)

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
  E.Tbl.clear tbl; (* be sure to reset temporary table *)
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

(* TODO: add signature for lambdas and handle congruence on lambdas.

   When adding `\x. t`, look at the DB depth of `t`. Lambda terms of distinct DB depths
    can never be merged, so we can just allocate a distinct fresh variable for each
   DB depth and add `t[x_db / x]` to the congruence with signature `Lam(t[x_db/x])`.
   When merging two such classes, the proof is [Thm.abs] which re-abstracts
   over `x_db`.

   TODO: also add some tests, like [(a=b), (\x. f(a,x)) c = f(a,c) |- (\x. f(b,x)) =b]
*)


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
  if Option.is_some sigt then (
    Vec.push self.to_update_sig @@ Update_sig node;
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
  | None -> assert (n1.root == n1); ()
  | Some (n2, e_12) ->
    reroot_at n2;
    assert (n2.expl == None);
    n2.expl <- Some (n1, e_12);
    n1.expl <- None;
    ()

(* main repair loop *)
let update (self:t) : unit =
  while not (Vec.is_empty self.to_merge && Vec.is_empty self.to_update_sig) do
    while not (Vec.is_empty self.to_update_sig) do
      let Update_sig n = Vec.pop_exn self.to_update_sig in
      begin match n.sigt with
        | None -> ()
        | Some s ->
          let s' = canon_sig s in
          match Sig_tbl.get self.sigs s' with
          | None -> Sig_tbl.add self.sigs s' n
          | Some n' when are_eq n n' -> ()
          | Some n' ->
            Vec.push self.to_merge @@ Merge (n,n',Exp_cong);
      end
    done;

    while not (Vec.is_empty self.to_merge) do
      let Merge (n1,n2,e_12) = Vec.pop_exn self.to_merge in
      let r1 = find n1 in
      let r2 = find n2 in
      if r1 != r2 then (
        (* add explanation for the merge *)
        reroot_at n1;
        assert (n1.expl == None);
        n1.expl <- Some (n2, e_12);
        (* merge r1 into r2 *)
        iter_class_ r1
          (fun n1' ->
             n1'.root <- r2;
             (* update signature of [parents(n1')] *)
             List.iter
               (fun n1'_p -> Vec.push self.to_update_sig @@ Update_sig n1'_p)
               n1'.parents);
        (* merge the equiv classes *)
        let n1_next = n1.next in
        n1.next <- n2.next;
        n2.next <- n1_next;
      )
    done
  done;
  ()

let add_thm_ (self:t) (th:K.thm) : bool =
  match E.unfold_eq (K.Thm.concl th) with
  | Some (a,b) ->
    let a = add_ self a in
    let b = add_ self b in
    if not (are_eq a b) then (
      Vec.push self.to_merge (Merge (a,b,Exp_merge th));
    );
    true
  | None ->
    false

let add_thm' self th = ignore (add_thm_ self th : bool)
let add_thm self th : unit =
  let ok = add_thm_ self th in
  if not ok then (
    Error.failf (fun k->k"cannot add non-equational theorem %a" K.Thm.pp_quoted th)
  )

let prove_cc_eqn (ctx:K.ctx) (hyps:K.thm list) (t:E.t) (u:E.t) : _ option =
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

let prove_cc_bool (ctx:K.ctx) (hyps:K.thm list) (concl: E.t) : _ option =
  match E.unfold_eq concl with
  | Some (t,u) -> prove_cc_eqn ctx hyps t u
  | None ->
    match List.partition (fun u -> Option.is_none (E.unfold_eq (K.Thm.concl u))) hyps with
    | [hyp_p], hyp_eqns ->
      begin match prove_cc_eqn ctx hyp_eqns (K.Thm.concl hyp_p) concl with
        | None -> None
        | Some cc_lemma ->
          (* by bool_eq on [… |- p], [eqns |- p=concl], we get
             [p, eqns |- concl] *)
          Some (K.Thm.bool_eq ctx hyp_p cc_lemma)
      end
    | _ ->
      Log.debugf 5 (fun k->k"prove_cc_bool: cannot pick a predicate hypothesis");
      None


let prove_cc_false
    (ctx:K.ctx) ~prove_false ~not_e
    (hyps:K.thm list) : _ option =
  let as_not e = match E.unfold_app e with
    | f, [u] when E.equal not_e f -> Some u
    | _ -> None
  in

  let pos, neg =
    hyps
    |> CCList.partition_filter_map
      (fun th ->
         let concl = K.Thm.concl th in
         match as_not concl with
         | None -> `Left (concl, th)
         | Some e' -> `Right (concl, e', th))
  in

  (* add all positive and negative terms to a CC *)
  let self = create ctx in
  let pos = pos |> List.map (fun (e,th) -> add_thm' self th; add_ self e, th) in
  let neg = neg |> List.map (fun (c,e,th) -> add_thm' self th; c, add_ self e, th) in

  update self;

  begin
    Iter.product (Iter.of_list pos) (Iter.of_list neg)
    |> Iter.find_map
      (fun ((n_pos, th_pos), (_concl_neg, n_neg, th_neg)) ->
         if find n_pos == find n_neg then (
           (* th1: [|- e_pos = e_neg] *)
           let th1 = prove_eq self n_pos n_neg in

           (* th2: [|- e_neg] via [th_pos] which is [|- e_pos] and [|- e_pos=e_neg] *)
           let th2 = K.Thm.bool_eq ctx th_pos th1 in

           (* th3: [|- false] from [|- e_neg] and [|- ¬ e_neg] (ie. th_neg) *)
           let th3 = prove_false ctx th2 th_neg in
           Some th3
         ) else (
           None
         ))
  end
