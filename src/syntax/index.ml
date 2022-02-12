
open Common_

(* TODO: at some point, if [qs] is too large, group them into sub-lists
   wrapped in a "queryable" that has as location the merge of all their locations.
   This is a very simple form of indexing *)

type idx = {
  qs: Queryable.t list;
  ty_envs: (Loc.t * Env.t) list;
}

type t =
  | Fake
  | Idx of idx

let empty : t = Idx {qs=[]; ty_envs=[]}
let fake : t = Fake

let size = function
  | Idx {qs;_} -> List.length qs
  | Fake -> 0

let find (self:t) (pos:Position.t) : Queryable.t list =
  let rec aux (q:Queryable.t) : _ list option =
    Log.debugf 20 (fun k->k"(@[examine queryable@ `%a`@ at %a@])" q#pp () Loc.pp q#loc);
    if Loc.contains q#loc pos then (
      Log.debugf 5 (fun k->k"(@[matched queryable@ `%a`@ at %a@])" q#pp () Loc.pp q#loc);
      let sub = Iter.find_map aux q#children |> Option.get_or ~default:[] in
      Some (q::sub)
    ) else None
  in
  begin match self with
  | Fake -> []
  | Idx {qs;_} ->
    match CCList.find_map aux qs with
    | None -> []
    | Some l -> List.rev l (* put deeper result first *)
  end

let update_ (self:t ref) ~f =
  begin match !self with
    | Idx idx -> self := Idx (f idx)
    | Fake -> ()
  end

let add_q (self:t ref) x : unit =
  update_ self ~f:(fun idx -> {idx with qs=x::idx.qs})
let add_env (self:t ref) env ~loc : unit =
  update_ self ~f:(fun idx -> {idx with ty_envs = (loc,env) :: idx.ty_envs})

let find_ty_env (self:t) (pos:Position.t) : Env.t =
  let rec find = function
    | [] -> Env.empty
    | (loc, env) :: _ when Loc.contains loc pos -> env
    | _ :: tl -> find tl
  in
  match self with
  | Fake -> Env.empty
  | Idx idx -> find idx.ty_envs
