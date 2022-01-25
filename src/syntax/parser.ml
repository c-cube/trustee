
module T = Token

type state = {
  lex: Token.t Lstream.t;
}

type 'a t = {
  run: 'b. state-> ok:('a -> 'b) -> err:(Error.t -> 'b) -> 'b;
} [@@unboxed]

let run lex self : _ result =
  self.run {lex} ~ok:(fun x -> Ok x) ~err:(fun e -> Error e)

let[@inline] return x : _ t = { run=fun _ ~ok ~err:_ -> ok x }
let[@inline] fail e : _ t = { run=fun _ ~ok:_ ~err -> err e }

let[@inline] ( let+ ) p1 f : _ t =
  { run=fun state ~ok ~err ->
        p1.run state ~err
          ~ok:(fun x1 -> ok (f x1))
  }

let[@inline] ( and+ ) p1 p2 = {
  run=fun state ~ok ~err ->
    p1.run state ~err ~ok:(fun x1 ->
        p2.run state ~err
          ~ok:(fun x2 -> ok (x1,x2)))
}

let[@inline] ( let* ) p1 f : _ t =
  { run=fun state ~ok ~err ->
        p1.run state ~err
          ~ok:(fun x1 ->
              let p2 = f x1 in
              p2.run state ~err ~ok)
  }

let ( <* ) p1 p2 =
  let+ x = p1
  and+ _ = p2 in x

let ( *> ) p1 p2 =
  let+ _ = p1
  and+ x = p2 in x

module Infix = struct
  let ( let+ ) = ( let+ )
  let ( let* ) = ( let* )
  let ( and+ ) = ( and+ )
  let ( *> ) = ( *> )
  let ( <* ) = ( <* )
end

let exact ?(msg="") tok : _ t = {
  run=fun state ~ok ~err ->
    let tok2, loc = Lstream.next state.lex in
    if T.equal tok tok2 then ok loc
    else err (Error.makef ~loc "expected `%a` but got `%a`@ %s"
                T.pp tok T.pp tok2 msg)
}

let exact' ?msg tok : _ =
  let+ _loc = exact ?msg tok in
  ()

(* careful, this is risky wrt termination *)
let[@inline] cur_ : (T.t * _) t =
  {run=fun state ~ok ~err:_ ->
      let tok, loc = Lstream.cur state.lex in
      ok (tok,loc)
  }


let loc : Loc.t t = let+ _, loc = cur_ in loc

let[@inline] next : (T.t * _) t =
  {run=fun state ~ok ~err:_ ->
      let tok, loc = Lstream.next state.lex in
      ok (tok,loc)
  }

let[@inline] fail_str msg : _ =
  let* loc = loc in
  fail (Error.make ~loc msg)

let[@inline] fail_strf fmt = Fmt.kasprintf fail_str fmt

let parsing f p = {
  run=fun state ~ok ~err -> p.run state ~ok ~err:(fun e -> err (f e))
}

let token_if ?(msg="") f : _ t = {
  run=fun state ~ok ~err ->
    let tok, loc = Lstream.next state.lex in
    if f tok then ok (tok,loc)
    else err (Error.makef ~loc "unexpected token `%a`@ %s" T.pp tok msg)
}

let switch_next f p_else : _ t = {
  run=fun state ~ok ~err ->
    let tok, loc = Lstream.cur state.lex in
    let b, p = f tok loc in
    begin match b with
      | `consume -> Lstream.consume state.lex;
      | `keep -> ()
    end;
    p.run state ~ok ~err
}

let (<|>) (tok,p1) p2 =
  switch_next @@ fun tok2 _ ->
  if Token.equal tok tok2 then `consume, p1 else `keep, p2

let eoi ~msg () = exact' ~msg T.EOF
let lbrace ?msg () = exact' ?msg T.LBRACE
let rbrace ?msg () = exact' ?msg T.RBRACE
let lparen ?msg () = exact' ?msg T.LPAREN
let rparen ?msg () = exact' ?msg T.RPAREN
let semi ?msg () = exact' ?msg T.SEMI_COLON
let sym : _ t =
  let* tok, _ = next in
  match tok with
  | T.SYM s -> return s
  | _ -> fail_str "expected a symbol"
