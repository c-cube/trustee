module K = Kernel
module E = K.Expr

type result =
  | Gt
  | Lt
  | Eq
  | Incomparable

type params = {
  var_as_cst: bool;
      (** if true, variables are just considered to be
      constants and are totally ordered in an unspecified but stable way.
      If false, then variables are incomparable and [a > b] implies that
      the multiset of variables of [a] contains the one of [b]. *)
  precedence: string -> string -> int;  (** Total order on constants *)
  weight: string -> int;
      (** Weight of constants. Must always be [>= 1]
      (we ignore the edge cases where one unary symbol can have weight 0
      for simplicity) *)
}

module KBO_ = struct
  type weight = int

  (* used to keep track of the balance of variables and the current
     weight difference *)
  type state = {
    mutable wb: weight;
    (* weight of LHS - weight of RHS *)
    mutable pos_counter: int;
    (* Number of variables occurring only positively (in first term) *)
    mutable neg_counter: int;
    (* Number of variables occurring only negatively (in second term) *)
    mutable balance: CCInt.t E.Tbl.t;
    (* State for one variable, where we could occurrences in the LHS and RHS terms. *)
    params: params;
  }

  let create params : state =
    {
      wb = 0;
      pos_counter = 0;
      neg_counter = 0;
      balance = E.Tbl.create 8;
      params;
    }

  (* add a positive variable *)
  let add_pos_var st var : unit =
    let n = E.Tbl.get_or st.balance var ~default:0 in
    if n = 0 then
      st.pos_counter <- st.pos_counter + 1
    else if n = -1 then
      st.neg_counter <- st.neg_counter - 1;
    E.Tbl.replace st.balance var (n + 1)

  (** add a negative variable *)
  let add_neg_var st var : unit =
    let n = E.Tbl.get_or st.balance var ~default:0 in
    if n = 0 then
      st.neg_counter <- st.neg_counter + 1
    else if n = 1 then
      st.pos_counter <- st.pos_counter - 1;
    E.Tbl.replace st.balance var (n - 1)

  let add_wb_ st x = st.wb <- st.wb + x

  let sub_wb_ st x = st.wb <- st.wb - x

  let incr_wb_ st = st.wb <- st.wb + 1

  let decr_wb_ st = st.wb <- st.wb - 1

  (* Update term balance, weight balance ([wb]), and check whether `t`
     contains the variable `s` *)
  let rec balance_weight st (e : E.t) (s : _ option) ~pos : bool =
    match E.view e with
    | E.E_kind | E.E_type | E.E_arrow _ | E.E_bound_var _ | E.E_box _ ->
      if pos then
        incr_wb_ st
      else
        decr_wb_ st;
      false
    | E.E_const (c, _) ->
      let wc = st.params.weight (K.Const.name c) in
      assert (wc > 0);
      if pos then
        add_wb_ st wc
      else
        sub_wb_ st wc;
      false
    | E.E_var v ->
      if pos then
        incr_wb_ st
      else
        decr_wb_ st;
      (* as if it were a constant of weight 1 *)
      if not st.params.var_as_cst then
        if pos then
          add_pos_var st e
        else
          add_neg_var st e;
      (match s with
      | Some s -> K.Var.equal s v
      | None -> false)
    | E.E_app (f, a) ->
      let r1 = balance_weight st f s ~pos in
      let r2 = balance_weight st a s ~pos in
      r1 || r2
    | E.E_lam (_, _ty, bod) ->
      if pos then
        incr_wb_ st
      else
        decr_wb_ st;
      balance_weight st bod s ~pos

  let balance_weight_rec (st : state) (es : E.t list) s ~pos : bool =
    List.fold_left
      (fun occurs e ->
        let r = balance_weight st e s ~pos in
        occurs || r)
      false es

  let rec tc_kbo st (t1 : E.t) (t2 : E.t) : result =
    if E.equal t1 t2 then
      Eq
    else (
      match E.view t1, E.view t2 with
      | E.E_var _, E.E_var _ ->
        add_pos_var st t1;
        add_neg_var st t2;
        Incomparable
      | E.E_var x, _ ->
        add_pos_var st t1;
        incr_wb_ st;
        let contains = balance_weight st t2 (Some x) ~pos:false in
        if contains then
          Lt
        else
          Incomparable
      | _, E.E_var x ->
        add_neg_var st t2;
        decr_wb_ st;
        let contains = balance_weight st t1 (Some x) ~pos:true in
        if contains then
          Gt
        else
          Incomparable
      | _ ->
        let f1, ts1 = E.unfold_app t1 in
        let f2, ts2 = E.unfold_app t2 in

        (* precedences for heads *)
        let cmp_p =
          match E.view f1, E.view f2 with
          | E.E_const (c1, _), E.E_const (c2, _) ->
            (* FIXME: if params.var_as_cst then also do variable cases *)
            let cmp =
              st.params.precedence (K.Const.name c1) (K.Const.name c2)
            in
            if cmp < 0 then
              Lt
            else if cmp = 0 then
              Eq
            else
              Gt
          | _ -> Incomparable
        in

        let (_ : bool) = balance_weight st f1 None ~pos:true in
        let (_ : bool) = balance_weight st f2 None ~pos:false in

        (* lexicographic comparison, if applicable *)
        let res_lex =
          match cmp_p with
          | Eq -> tc_kbo_lex st ts1 ts2
          | _ ->
            let (_ : bool) = balance_weight_rec st ts1 None ~pos:true in
            let (_ : bool) = balance_weight_rec st ts2 None ~pos:false in
            Incomparable
        in

        let l_or_none =
          if st.neg_counter = 0 then
            Lt
          else
            Incomparable
        in
        let g_or_none =
          if st.pos_counter = 0 then
            Gt
          else
            Incomparable
        in

        (* now consider: weight, then precedence *)
        if st.wb > 0 then
          g_or_none
        else if st.wb < 0 then
          l_or_none
        else if cmp_p = Gt then
          g_or_none
        else if cmp_p = Lt then
          l_or_none
        else if cmp_p = Eq then (
          match res_lex with
          | Eq -> Eq
          | Lt -> l_or_none
          | Gt -> g_or_none
          | Incomparable -> Incomparable
        ) else
          Incomparable
    )

  (* lexicographic order *)
  and tc_kbo_lex st (ts1 : E.t list) (ts2 : E.t list) : result =
    match ts1, ts2 with
    | [], [] -> Eq
    | [], _ ->
      let (_ : bool) = balance_weight_rec st ts2 None ~pos:false in
      Lt
    | _, [] ->
      let (_ : bool) = balance_weight_rec st ts1 None ~pos:true in
      Gt
    | t1 :: ts1, t2 :: ts2 ->
      (match tc_kbo st t1 t2 with
      | Eq -> tc_kbo_lex st ts1 ts2 (* continue on the rest of the lists *)
      | r ->
        (* balance weights and return r *)
        let (_ : bool) = balance_weight_rec st ts1 None ~pos:true in
        let (_ : bool) = balance_weight_rec st ts2 None ~pos:false in
        r)
end

let default_params () =
  { var_as_cst = false; weight = (fun _ -> 1); precedence = String.compare }

let compare ?(params = default_params ()) (e1 : E.t) (e2 : E.t) : result =
  let st = KBO_.create params in
  KBO_.tc_kbo st e1 e2

let lt ?params a b : bool = compare ?params a b = Lt

let gt ?params a b : bool = compare ?params a b = Gt
