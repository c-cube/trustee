open OUnit2
module Enc = Trustee_minidag.Encode
module Dec = Trustee_minidag.Decode
module Slice = Trustee_minidag.Slice
module Proof_zip = Trustee_opentheory.Proof_zip

let encode f =
  let buf = Buffer.create 128 in
  let out =
    object
      method write b o l = Buffer.add_subbytes buf b o l
    end
  in
  let enc = Enc.create ~out () in
  let r = f enc in
  Enc.flush enc;
  Buffer.contents buf, r

let is_stop s i = Char.code (String.unsafe_get s i) lsr 4 = 0

let refs data off =
  let dec = Dec.create data in
  Dec.read_node dec off (fun nd _cmd ->
      let acc = ref [] in
      let rec loop () =
        if not (is_stop data nd.off) then (
          match Dec.read nd with
          | Dec.Ref r ->
            acc := r :: !acc;
            loop ()
          | _ -> loop ()
        )
      in
      loop ();
      List.rev !acc)

let cmd data off =
  let dec = Dec.create data in
  Dec.read_node dec off (fun _nd cmd -> cmd)

let first_string data off =
  let dec = Dec.create data in
  Dec.read_node dec off (fun nd _cmd -> Dec.read_string_exn nd)

let mk_graph () =
  encode (fun enc ->
      let n0 =
        Enc.write_node enc "v" (fun nd ->
            Enc.string nd "x";
            Enc.int nd 0)
      in
      let n1 =
        Enc.write_node enc "v" (fun nd ->
            Enc.string nd "y";
            Enc.int nd 1)
      in
      let n2 =
        Enc.write_node enc "seq" (fun nd ->
            Enc.ref nd n0;
            Enc.ref nd n1)
      in
      ignore
        (Enc.write_node enc "dead" (fun nd -> Enc.blob nd (String.make 512 'z')));
      n0, n1, n2)

let mk_other () =
  encode (fun enc ->
      let n0 =
        Enc.write_node enc "v" (fun nd ->
            Enc.string nd "z";
            Enc.int nd 2)
      in
      let n1 = Enc.write_node enc "root2" (fun nd -> Enc.ref nd n0) in
      n0, n1)

let test_slice_drops_unreachable _ctx =
  let data, (_n0, _n1, n2) = mk_graph () in
  let sliced, root = Slice.slice ~data ~root:n2 in
  assert_bool "slice is smaller" (String.length sliced < String.length data);
  assert_equal "seq" (cmd sliced root);
  assert_equal [ "x"; "y" ] (List.map (first_string sliced) (refs sliced root));
  List.iter
    (fun r -> assert_bool "ref in slice" (r >= 0 && r < root))
    (refs sliced root)

let test_merge_remaps_roots _ctx =
  let data, (_n0, _n1, n2) = mk_graph () in
  let other, (_m0, m1) = mk_other () in
  let s1, r1 = Slice.slice ~data ~root:n2 in
  let s2, r2 = Slice.slice ~data:other ~root:m1 in
  let merged = Slice.merge [ s1, r1; s2, r2 ] in
  match merged with
  | data, [ root1; root2 ] ->
    assert_equal "seq" (cmd data root1);
    assert_equal [ "x"; "y" ] (List.map (first_string data) (refs data root1));
    assert_equal "root2" (cmd data root2);
    assert_equal "z" (first_string data (List.hd (refs data root2)))
  | _ -> assert_failure "unexpected merge roots"

let test_merge_shifts_refs _ctx =
  (* Merging shifts every ref; when a shift grows a ref's encoding, later nodes
     move, so [base + offset] remapping points into the middle of nodes. *)
  let s1, r1 =
    let data, root =
      encode (fun enc ->
          Enc.write_node enc "v" (fun nd ->
              Enc.string nd (String.make 300 'p');
              Enc.int nd 0))
    in
    Slice.slice ~data ~root
  in
  let s2, r2 =
    let data, root =
      encode (fun enc ->
          let l =
            Enc.write_node enc "v" (fun nd ->
                Enc.string nd "l";
                Enc.int nd 0)
          in
          let x =
            Enc.write_node enc "@" (fun nd ->
                Enc.ref nd l;
                Enc.ref nd l)
          in
          let t =
            Enc.write_node enc "v" (fun nd ->
                Enc.string nd "t";
                Enc.int nd 0)
          in
          Enc.write_node enc "@" (fun nd ->
              Enc.ref nd x;
              Enc.ref nd t))
    in
    Slice.slice ~data ~root
  in
  assert_bool "first slice is past the 1-byte ref limit"
    (String.length s1 > 0x100);
  assert_bool "second slice is not empty" (String.length s2 > 0);
  match Slice.merge [ s1, r1; s2, r2 ] with
  | data, [ _; root2 ] ->
    let starts = ref [] in
    let dec = Dec.create data in
    Dec.iter_nodes dec (fun off _cmd _args -> starts := off :: !starts);
    let starts = !starts in
    assert_bool "root is a node start" (List.mem root2 starts);
    Dec.iter_nodes dec (fun off _cmd _args ->
        List.iter
          (fun r ->
            assert_bool
              (Printf.sprintf "ref %d from node %d is a node start" r off)
              (List.mem r starts))
          (refs data off));
    assert_equal "t" (first_string data (List.nth (refs data root2) 1))
  | _ -> assert_failure "unexpected merge roots"

let temp_zip () =
  Filename.temp_file ~temp_dir:(Sys.getcwd ()) "trustee_test" ".zip"

let with_zip f =
  let path = temp_zip () in
  Fun.protect
    ~finally:(fun () -> try Sys.remove path with _ -> ())
    (fun () -> f path)

let append_footer data =
  let dec = Dec.create data in
  let last = ref 0 in
  Dec.iter_nodes dec (fun off _cmd _args -> last := off);
  let last_size = String.length data - !last in
  let footer = Bytes.create 16 in
  Bytes.set_int64_le footer 0 (Int64.of_int last_size);
  Bytes.set_int64_le footer 8 0x504F4F462E454E54L;
  data ^ Bytes.unsafe_to_string footer

let first_ref data node =
  let dec = Dec.create data in
  Dec.read_node dec node (fun nd _cmd ->
      ignore (Dec.read_int64_exn nd);
      Dec.read_ref_exn nd)

let last_ref data node =
  let dec = Dec.create data in
  Dec.read_node dec node (fun nd _cmd ->
      let n = Int64.to_int (Dec.read_int64_exn nd) in
      let last = ref 0 in
      for _ = 1 to n do
        last := Dec.read_ref_exn nd
      done;
      !last)

let step_concl data step =
  let dec = Dec.create data in
  Dec.read_node dec step (fun nd _cmd -> Dec.read_ref_exn nd)

let build_zip path =
  let data, _root =
    encode (fun enc ->
        let ty = Enc.write_node enc "T" (fun _ -> ()) in
        let ce name =
          Enc.write_node enc "ce" (fun nd ->
              Enc.string nd name;
              Enc.ref nd ty;
              Enc.string nd "ar";
              Enc.int nd 0)
        in
        let ce1 = ce "test.p" in
        let ce2 = ce "nodef.p" in
        let concl = Enc.write_node enc "bool" (fun _ -> ()) in
        let step =
          Enc.write_node enc "step" (fun nd ->
              Enc.ref nd concl;
              Enc.string nd "axiom";
              Enc.int nd 0)
        in
        let lp =
          Enc.write_node enc "lp" (fun nd ->
              Enc.int nd 1;
              Enc.ref nd step)
        in
        let proofs =
          Enc.write_node enc "proofs" (fun nd ->
              Enc.int nd 1;
              Enc.ref nd lp)
        in
        Enc.write_node enc "theory" (fun nd ->
            Enc.int nd 0;
            Enc.int nd 0;
            Enc.int nd 2;
            Enc.ref nd ce1;
            Enc.ref nd ce2;
            Enc.int nd 0;
            Enc.ref nd proofs))
  in
  let data = append_footer data in
  let def_data, _ =
    encode (fun enc ->
        let var =
          Enc.write_node enc "v" (fun nd ->
              Enc.string nd "x";
              Enc.int nd 0)
        in
        let body =
          Enc.write_node enc "v" (fun nd ->
              Enc.string nd "def";
              Enc.int nd 0)
        in
        Enc.write_node enc "dt" (fun nd ->
            Enc.int nd 1;
            Enc.ref nd var;
            Enc.ref nd body))
  in
  let zf = Zip.open_out path in
  Zip.add_entry data zf "tiny.entry";
  Zip.add_entry def_data zf "_storage/cdef:test.p";
  Zip.close_out zf;
  data

let build_multistep_zip path =
  let data, _ =
    encode (fun enc ->
        let v name =
          Enc.write_node enc "v" (fun nd ->
              Enc.string nd name;
              Enc.int nd 0)
        in
        let parent = v "parent" in
        let theorem = v "theorem" in
        let seq e = Enc.write_node enc "seq" (fun nd -> Enc.ref nd e) in
        let s0 = seq parent in
        let s1 = seq theorem in
        let step s rule =
          Enc.write_node enc "step" (fun nd ->
              Enc.ref nd s;
              Enc.string nd rule;
              Enc.int nd 0)
        in
        let st0 = step s0 "lemma" in
        let st1 = step s1 "axiom" in
        let lp =
          Enc.write_node enc "lp" (fun nd ->
              Enc.int nd 2;
              Enc.ref nd st0;
              Enc.ref nd st1)
        in
        let proofs =
          Enc.write_node enc "proofs" (fun nd ->
              Enc.int nd 1;
              Enc.ref nd lp)
        in
        Enc.write_node enc "theory" (fun nd ->
            Enc.int nd 0;
            Enc.int nd 0;
            Enc.int nd 0;
            Enc.int nd 0;
            Enc.ref nd proofs))
  in
  let data = append_footer data in
  let zf = Zip.open_out path in
  Zip.add_entry data zf "multi.entry";
  Zip.close_out zf

let test_blob_access _ctx =
  with_zip (fun path ->
      let full = build_zip path in
      let zh = Proof_zip.open_zip path in
      Fun.protect
        ~finally:(fun () -> Proof_zip.close_zip zh)
        (fun () ->
          assert_equal (Some full) (Proof_zip.entry_bytes zh "tiny");
          assert_equal None (Proof_zip.entry_bytes zh "missing");
          (match Proof_zip.slice_proof_blob zh ~name:"tiny" ~idx:0 with
          | None -> assert_failure "missing proof slice"
          | Some (data, root) ->
            assert_bool "proof slice smaller"
              (String.length data < String.length full);
            assert_equal "lp" (cmd data root));
          assert_equal None (Proof_zip.slice_proof_blob zh ~name:"tiny" ~idx:1);
          assert_equal None (Proof_zip.slice_proof_blob zh ~name:"nope" ~idx:0);
          (match Proof_zip.slice_const_blob zh ~name:"tiny" ~const:"test.p" with
          | None -> assert_failure "missing const slice"
          | Some (data, root, def_root) ->
            assert_equal "ce" (cmd data root);
            assert_equal "test.p" (first_string data root);
            (match def_root with
            | None -> assert_failure "missing def root"
            | Some (droot, dcmd) ->
              assert_equal "v" (cmd data droot);
              assert_equal "def" (first_string data droot);
              assert_equal "dt" dcmd));
          match Proof_zip.slice_const_blob zh ~name:"tiny" ~const:"nodef.p" with
          | None -> assert_failure "missing nodef const slice"
          | Some (data, root, def_root) ->
            assert_equal "nodef.p" (first_string data root);
            assert_equal None def_root;
            ignore root))

let test_multistep_last_concl _ctx =
  with_zip (fun path ->
      build_multistep_zip path;
      let zh = Proof_zip.open_zip path in
      Fun.protect
        ~finally:(fun () -> Proof_zip.close_zip zh)
        (fun () ->
          assert_equal (Some 1) (Proof_zip.proof_count zh ~name:"multi");
          match Proof_zip.slice_proof_blob zh ~name:"multi" ~idx:0 with
          | None -> assert_failure "missing proof slice"
          | Some (data, lp_root) ->
            let first_step = first_ref data lp_root in
            let last_step = last_ref data lp_root in
            assert_bool "multiple steps" (first_step <> last_step);
            let first_concl = step_concl data first_step in
            let last_concl = step_concl data last_step in
            assert_equal "parent"
              (first_string data (List.hd (refs data first_concl)));
            assert_equal "theorem"
              (first_string data (List.hd (refs data last_concl)))))

let suite =
  "minidag_slice"
  >::: [
         "slice_drops_unreachable" >:: test_slice_drops_unreachable;
         "merge_remaps_roots" >:: test_merge_remaps_roots;
         "merge_shifts_refs" >:: test_merge_shifts_refs;
         "blob_access" >:: test_blob_access;
         "multistep_last_concl" >:: test_multistep_last_concl;
       ]

let () = OUnit2.run_test_tt_main suite
