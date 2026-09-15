open Zdatatype

let run_test source_file =
  Statistic.clear ();
  let root = Sys.getenv "DUNE_SOURCEROOT" in
  Sys.chdir root;
  let cfg_root = Yojson.Safe.from_file "test/meta-config.json" in
  TypecheckerConfig.bootstrap cfg_root;
  let source_file = Filename.concat root source_file in
  let code = Preprocess.preprocess [ source_file ] in
  let results = Typing.struc_check (Preprocess.load_bctx ()) code in
  let passed =
    List.filter_map (fun (n, ok) -> if ok then Some n else None) results
  in
  let failed =
    List.filter_map (fun (n, ok) -> if ok then None else Some n) results
  in
  Printf.printf "passing: %s\n" (List.split_by_comma Fun.id passed);
  Printf.printf "failing: %s\n" (List.split_by_comma Fun.id failed)
