
let spf = Printf.sprintf

type sub = {
  sub_name: string;
  imports: string list;
  package: string option;
}

type t = {
  name: string;
  version: string;
  meta: (string * string) list;
  subs: sub list;
  main: sub;
}

let equal a b = a.name = b.name
let hash a = CCHash.string a.name

let pp_kv k out v = Fmt.fprintf out "%s: %s" k v
let pp_sub out (s:sub) =
  Fmt.fprintf out "@[<v2>%s {@,%a%a@;<0 -2>}@]"
    s.sub_name
    Fmt.(list ~sep:(return "@ ") (pp_kv "import:")) s.imports
    Fmt.(some (pp_kv "@,package:")) s.package

let pp out (self:t) : unit =
  Fmt.fprintf out "@[<v>name: %s@," self.name;
  List.iter (fun (k,v) -> Fmt.fprintf out "%s: %s@," k v) self.meta;
  List.iter (fun sub -> Fmt.fprintf out "%a@," pp_sub sub) self.subs;
  Fmt.fprintf out "@]"

let name self = self.name
let versioned_name self = spf "%s-%s" self.name self.version

let requires self : _ list =
  self.meta
  |> CCList.filter_map
    (function ("requires", s) -> Some s | _ -> None)

let sub_packages self : _ list =
  let l = ref [] in
  List.iter
    (fun sub ->
       match sub.package with
       | None -> ()
       | Some s -> l := s :: !l)
    self.subs;
  !l

module P = CCParse

type item =
  | I_kv of string * string
  | I_sub of string * item list

let parse : t P.t =
  let open P.Infix in

  let pkey =
    P.chars1_if (function 'a'..'z'|'A'..'Z'|'0'..'9'|':'|'-' -> true | _ -> false)
  in
  let rec pitem key =
    if CCString.suffix ~suf:":" key then (
      let key = String.sub key 0 (String.length key-1) in
      P.skip_space *> P.chars1_if (function '\n' -> false | _ -> true)
      >>= fun v ->
      P.return (I_kv (key,v))
    ) else (
      P.skip_space *> P.char '{' *> P.skip_white *>
      pitems [] >>= fun l ->
      P.skip_white *>
      P.return (I_sub (key, l))
    )
  and pitems acc =
    P.skip_white *>
    ((P.try_ P.eoi *> P.return (List.rev acc))
     <|> (P.try_ (P.char '}') *> P.return (List.rev acc))
     <|> (P.try_ pkey >>= fun key ->
          pitem key >>= fun i ->
          pitems (i::acc))
     <?> "expected items")
  in
  pitems [] >>= fun items ->

  let find ~msg l f =
    match CCList.find_map f l with
    | Some v -> v
    | None -> failwith (msg())
  in

  try
    let name =
      find items (function (I_kv ("name",s)) -> Some s | _ -> None)
        ~msg:(fun () -> "no `name` provided")
    and version =
      find items (function (I_kv ("version",s)) -> Some s | _ -> None)
        ~msg:(fun () -> "no `version` provided")
    in
    let meta =
      CCList.filter_map
        (function
          | (I_kv (("name" | "version"),_)) -> None
          | I_kv (k,v) -> Some (k,v)
          | I_sub _ -> None)
        items
    in
    let subs =
      CCList.filter_map
        (function
          | I_kv _ -> None
          | I_sub (sub_name,l) ->
            let imports =
              CCList.filter_map
                (function
                  | (I_kv ("import",s)) -> Some s | _ -> None)
                l
            in
            let package =
              CCList.find_map
                (function (I_kv ("package",s)) -> Some s | _ -> None) l
            in
            Some {sub_name; imports; package}
        )
      items
    in
    let main = find subs (fun s -> if s.sub_name="main" then Some s else None)
        ~msg:(fun() -> "no `main` entry")
    in
    let subs = List.filter (fun s -> s.sub_name <> "main") subs in
    P.return {name; version; meta; subs; main}
  with Failure s -> P.fail s

let of_string s =
  match P.parse_string parse s with
  | Ok x -> Ok x
  | Error e -> Error (Trustee_error.mk e)

module List_dir = struct
  type thy = t
  type path = string

  (** Results of listing a directory *)
  type t = {
    theories: (path * thy) list;
    errors: (path * Trustee_error.t) list;
  }

  (* gen *)
  module G = struct
    let rec iter ~f g = match g() with
      | Some x -> f x; iter ~f g
      | None -> ()
  end

  let list_dir dir : t =
    let errors = ref [] in
    let theories = ref [] in
    let g = CCIO.File.walk dir in
    let module E = Trustee_error in
    G.iter g
      ~f:(fun (k,file) ->
          if k=`File && CCString.suffix ~suf:".thy" file then (
            try
              let s = CCIO.File.read_exn file in
              match of_string s with
              | Ok thy -> theories := (file,thy) :: !theories
              | Error e -> errors := (file,e) :: !errors
            with e ->
              errors := (file, Trustee_error.mk (Printexc.to_string e)) :: !errors;
          ));
    { theories= !theories;
      errors= !errors;
    }
end
