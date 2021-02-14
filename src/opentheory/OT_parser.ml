
module K = Trustee_core.Kernel
module Log = Trustee_core.Log

type input = {
  iter_lines: string Iter.t;
}

module Input = struct
  type t = input

  let rec iter_g f g = match g() with
    | None -> ()
    | Some s -> f s; iter_g f g

  let of_string s : t  =
    let iter_lines = CCString.Split.iter_cpy ~by:"\n" s in
    {iter_lines}

  let of_chan ic =
    let iter_lines = fun yield -> iter_g yield (CCIO.read_lines_gen ic) in
    {iter_lines}

  (* TODO: camlzip: dezip + of_string *)
end

module Name = struct
  type t = {
    path: string list;
    name: string;
  }

  let to_string (self:t) =
    match self.path with
    | [] -> self.name
    | ps -> String.concat "." ps ^ "." ^ self.name
  let pp out self = Fmt.string out (to_string self)
end

module Article = struct
  type t = {
    consts: K.Const.t list;
    axioms: K.Thm.t list;
    theorems: K.Thm.t list;
  }

  type item =
    | I_cst of K.Const.t
    | I_axiom of K.Thm.t
    | I_thm of K.Thm.t

  let items self =
    Iter.append_l [
      Iter.of_list self.consts |> Iter.map (fun c->I_cst c);
      Iter.of_list self.axioms |> Iter.map (fun th->I_axiom th);
      Iter.of_list self.theorems |> Iter.map (fun th->I_thm th);
    ]

  let pp_item out = function
    | I_cst c -> Fmt.fprintf out "(@[const %a@])" K.Const.pp c
    | I_axiom th -> Fmt.fprintf out "(@[axiom %a@])" K.Thm.pp_quoted th
    | I_thm th -> Fmt.fprintf out "(@[theorem %a@])" K.Thm.pp_quoted th

  let pp out (self:t) =
    Fmt.fprintf out "@[<v>art {@,%a@<1 -4>}@]"
      (Fmt.iter pp_item) (items self)
  let to_string = Fmt.to_string pp
end

module OT = struct
  type name = string list * string

  type ty_op = string * (K.ctx -> K.ty list -> K.ty)
  type const = string * (K.ctx -> K.expr list -> K.expr)

  type obj =
    | O_int of int
    | O_string of string
    | O_name of Name.t
    | O_ty of K.ty
    | O_ty_op of ty_op
    | O_const of const
    | O_var of K.var
    | O_term of K.expr
    | O_thm of K.thm
    | O_list of obj list

  let rec pp_obj out = function
    | O_int i -> Fmt.int out i
    | O_string s -> Fmt.fprintf out "%S" s
    | O_name n -> Name.pp out n
    | O_ty ty -> Fmt.fprintf out "@[ty: %a@]" K.Expr.pp ty
    | O_ty_op (c,_) -> Fmt.fprintf out "@[ty-const: %s@]" c
    | O_const (c,_) -> Fmt.fprintf out "@[const: %s@]" c
    | O_var v -> Fmt.fprintf out "@[var: %a@]" K.Var.pp v
    | O_term e -> Fmt.fprintf out "@[term: %a@]" K.Expr.pp e
    | O_thm th -> Fmt.fprintf out "@[thm: %a@]" K.Thm.pp_quoted th
    | O_list l -> Fmt.Dump.list pp_obj out l

  type state = {
    ctx: K.ctx;
    input: input;
    mutable stack: obj list;
    dict: (int, obj) Hashtbl.t;
    mutable consts: K.const list;
    mutable axioms: K.Thm.t list;
    mutable theorems: K.Thm.t list;
  }

  let pp out (self:state) : unit =
    Fmt.fprintf out "{@[stack:@ %a;@ dict={@[%a@]}@]}"
      (Fmt.Dump.list pp_obj) self.stack
      (Fmt.iter Fmt.Dump.(pair int pp_obj)) (CCHashtbl.to_iter self.dict)

  (* a rule associated with a keyword *)
  type rule = state -> unit

  let version : rule = fun self ->
    match self.stack with
    | O_int 6 :: st -> self.stack <- st
    | O_int n :: _ -> errorf (fun k->k"expected version to be '6', not %d" n)
    | _ -> errorf (fun k->k"version: expected an integer")

  let absTerm : rule = fun self ->
    match self.stack with
    | O_term b :: O_var v :: st ->
      let t = K.Expr.lambda self.ctx v b in
      self.stack <- O_term t :: st;
    | _ -> errorf (fun k->k"cannot apply absTerm@ in state %a" pp self)

  let absThm : rule = fun self ->
    match self.stack with
    | O_thm th :: O_var v :: st ->
      let th = K.Thm.abs self.ctx th v in
      self.stack <- O_thm th :: st;
    | _ -> errorf (fun k->k"cannot apply absThm@ in state %a" pp self)

  let typeOp : rule = fun self ->
    match self.stack with
    | O_string  s :: st ->
      let f_op = match s with
        | "->" ->
          (fun ctx -> function
             | [a;b] -> K.Expr.arrow ctx a b
             | _ -> error "arrow expects 2 args")
        | "bool" ->
          (fun ctx -> function [] -> K.Expr.bool ctx | _ -> error "bool is a const")
        | _ -> errorf (fun k->k"unknown type operator '%s'" s)
      in
      let op = "->", f_op in
      self.stack <- O_ty_op op :: st;
    | _ -> errorf (fun k->k"cannot apply typeOp@ in state %a" pp self)

  let def : rule = fun self ->
    match self.stack with
    | O_int i :: x :: st ->
      self.stack <- x :: st;
      Hashtbl.replace self.dict i x
    | _ -> errorf (fun k->k"cannot apply def@ in state %a" pp self)

  let varType : rule = fun self ->
    match self.stack with
    | O_string s :: st ->
      let v = K.Var.make s (K.Expr.type_ self.ctx) in
      self.stack <- O_ty (K.Expr.var self.ctx v) :: st;
    | _ -> errorf (fun k->k"cannot apply varType@ in state %a" pp self)

  let nil : rule = fun self -> self.stack <- O_list [] :: self.stack

  let cons : rule = fun self ->
    match self.stack with
    | O_list l :: o :: st ->
      self.stack <- O_list (o::l) :: st
    | _ -> errorf (fun k->k"cannot apply cons@ in state %a" pp self)

  let opType : rule = fun self ->
    match self.stack with
    | O_list l :: O_ty_op (_,op) :: st ->
      let args = l |> List.map (function
          | O_ty ty -> ty
          | o -> errorf (fun k->k"typeOp: %a is not a type" pp_obj o))
      in
      let ty = op self.ctx args in
      self.stack <- O_ty ty :: st;
    | _ -> errorf (fun k->k"cannot apply typeOp@ in state %a" pp self)

  let var : rule = fun self ->
    match self.stack with
    | O_ty ty :: O_string n :: st ->
      let v = K.Var.make n ty in
      self.stack <- O_var v :: st
    | O_ty ty :: O_name n :: st ->
      let v = K.Var.make (Name.to_string n) ty in
      self.stack <- O_var v :: st
    | _ -> errorf (fun k->k"cannot apply var@ in state %a" pp self)

  let const : rule = fun self ->
    let mk_ s st =
      let f_op = match s with
        | "=" ->
          (fun ctx -> function [a;b] -> K.Expr.app_eq ctx a b
                             | _ -> error "= is binary")
        | _ -> errorf (fun k->k"unknown const '%s'" s)
      in
      self.stack <- O_const (s, f_op) :: st
    in
    match self.stack with
    | O_string s :: st -> mk_ s st
    | O_name n :: st -> mk_ (Name.to_string n) st
    | _ -> errorf (fun k->k"cannot apply const@ in state %a" pp self)

  let ref_ : rule = fun self ->
    match self.stack with
    | O_int i :: st ->
      (try self.stack <- Hashtbl.find self.dict i :: st
       with Not_found -> errorf (fun k->k"undefined ref %d" i))
    | _ -> errorf (fun k->k"cannot apply ref@ in state %a" pp self)

  let rules : rule Str_map.t = [
    "version", version;
    "absTerm", absTerm;
    "absThm", absThm;
    "typeOp", typeOp;
    "def", def;
    "varType", varType;
    "nil", nil;
    "cons", cons;
    "opType", opType;
    "var", var;
    "const", const;
    "ref", ref_;
  ] |> Str_map.of_list

  let parse_and_check_art (ctx:K.ctx) (input:input) : Article.t or_error =
    Log.debug 5 "(open-theory.parse-and-check-art)";
    let self = {
      ctx; input; stack=[]; dict=Hashtbl.create 32;
      axioms=[]; theorems=[]; consts=[];
    } in
    let i = ref 0 in

    (* how to parse one line *)
    let process_line (s:string) : unit =
      let s = String.trim s in
      if s="" then errorf (fun k->k"empty line (at line %d)" !i);

      Log.debugf 50 (fun k->k"(@[ot: cur state is@ %a@])" pp self);
      Log.debugf 20 (fun k->k"(@[ot: process line: %s@])" s);

      begin match s.[0] with
        | '0' .. '9' | '-' ->
          let n =
            (try int_of_string s
             with _ -> errorf (fun k->k"invalid integer at line %d" !i))
          in
          self.stack <- O_int n :: self.stack
        | '"' ->
          let n = String.length s in
          if s.[n-1] <> '"' then errorf (fun k->k"expected closing \" at line %d" !i);
          let s = String.sub s 1 (n-2) in
          self.stack <- O_string s :: self.stack
        | _ ->
          begin match Str_map.find s rules with
            | r -> r self
            | exception Not_found ->
              errorf (fun k->k"unknown rule '%s' at line %d" s !i)
          end
      end;
      incr i;
    in
    try
      input.iter_lines process_line;
      let art = {
        Article.consts=self.consts;
        theorems=self.theorems;
        axioms=self.axioms;
      } in
      Ok art
    with Trustee_error.E e -> Error e
end

let parse_and_check_art = OT.parse_and_check_art

