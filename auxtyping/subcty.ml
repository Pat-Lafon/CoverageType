open Language
open Zutils
open Prop
open Zdatatype

let layout_qt = function Nt.Fa -> "∀" | Nt.Ex -> "∃"

let layout_qv { x = qt, x; ty } =
  spf "%s%s:{%s}" (layout_qt qt) x @@ layout_cty ty

let layout_vs qt uqvs =
  List.split_by_comma layout_qv
  @@ List.map (fun { x; ty } -> { x = (qt, x); ty }) uqvs

let layout_prop_ = layout_prop

let smart_dependent_forall (x, { nty; phi }) query =
  let phi = subst_prop_instance default_v (AVar x#:nty) phi in
  smart_forall_phi (x#:nty, phi) query

let smart_dependent_exists (x, { nty; phi }) query =
  let phi = subst_prop_instance default_v (AVar x#:nty) phi in
  smart_exists_phi (x#:nty, phi) query

let dump_dir = Sys.getenv_opt "POIROT_SMT_DUMP"
let dump_count = ref 0

(* Runs the axiom selection [Prover.check_sat] is about to run, labelling each
   axiom's assert with its name; the goal goes last, unlabelled. *)
let dump_query prop =
  match dump_dir with
  | None -> ()
  | Some dir ->
      let Prover.{ ctx; _ } = Prover.get_prover () in
      let names, axioms = List.split @@ Prover.select_axioms prop in
      let to_z3 = Propencoding.to_z3 ctx in
      let axioms = List.map to_z3 axioms and goal = to_z3 prop in
      (* The solver prints the declarations, then the asserts. *)
      let solver = Z3.Solver.mk_solver ctx None in
      Z3.Solver.add solver (axioms @ [ goal ]);
      let printed = Z3.Solver.to_string solver in
      let decls =
        String.sub printed 0
          (Core.String.substr_index_exn printed ~pattern:"(assert")
      in
      let labelled =
        List.map2
          (fun name e ->
            spf "(assert (! %s :named %s))\n" (Z3.Expr.to_string e) name)
          names axioms
      in
      incr dump_count;
      Core.Out_channel.write_all
        (spf "%s/q%03i.smt2" dir !dump_count)
        ~data:
          (spf "(set-option :timeout %i)\n%s%s(assert %s)\n(check-sat)\n"
             (ZUtilsConfig.get_prover_timeout_bound ())
             decls (String.concat "" labelled) (Z3.Expr.to_string goal))

let simplify_sub_typectx ctx (rty1, rty2) =
  let ctx = Typectx.ctx_to_list ctx in
  let rec aux (prefix, rest) (rty1, rty2) =
    match rest with
    | [] -> (prefix, rty1, rty2)
    | { x; ty } :: rest -> (
        match ty with
        | RtyBase { cty; _ } -> (
            match is_eq_phi default_v#:cty.nty cty.phi with
            | Some lit ->
                let rty1 = subst_cty_instance x lit rty1 in
                let rty2 = subst_cty_instance x lit rty2 in
                let rest =
                  List.map
                    (fun y -> { x = y.x; ty = subst_rty_instance x lit y.ty })
                    rest
                in
                aux (prefix, rest) (rty1, rty2)
            | None -> aux (prefix @ [ { x; ty } ], rest) (rty1, rty2))
        | _ -> aux (prefix @ [ { x; ty } ], rest) (rty1, rty2))
  in
  aux ([], ctx) (rty1, rty2)

let sub_cty ou rctx cty1 cty2 =
  let ctx_list, cty1, cty2 = simplify_sub_typectx rctx.rty_ctx (cty1, cty2) in
  let () =
    TypecheckerLog.auxtyping @@ fun _ ->
    Printf.printf "ctx_list: %s\n" (List.split_by_comma _get_x ctx_list)
  in
  let overctx, underctx = build_wf_ctx ctx_list in
  let () =
    TypecheckerLog.auxtyping @@ fun _ ->
    let overctx =
      List.map (fun (x, cty) -> x#:(RtyBase { ou = Over; cty })) overctx
    in
    let underctx =
      List.map (fun (x, cty) -> x#:(RtyBase { ou = Under; cty })) underctx
    in
    let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
    Typectx.pprint_ctx layout_rty ctx';
    print_newline ()
  in
  let () =
    let dom = List.map fst (overctx @ underctx) in
    if not (is_close_cty dom cty1) then (
      Printf.printf
        "left-hand-side type %s\n\
         %s should be closed under over + under ctx: [ %s ]\n"
        (* (layout_rty (RtyBase { ou; cty = cty1 })) *)
        (show_prop cty1.phi)
        (StrList.to_string (fv_cty_id cty1))
        (StrList.to_string dom);
      _die [%here])
  in
  let () =
    let dom = List.map fst (overctx @ underctx) in
    if not (is_close_cty dom cty2) then (
      Printf.printf
        "right-hand-side type %s\n\
        \ %s should be closed under over + under ctx: [ %s ]\n"
        (layout_rty (RtyBase { ou; cty = cty2 }))
        (StrList.to_string (fv_cty_id cty2))
        (StrList.to_string dom);
      _die [%here])
  in
  let nty = if Nt.equal_nt cty1.nty cty2.nty then cty1.nty else _die [%here] in
  let overctx_with_v = (default_v, mk_top_cty nty) :: overctx in
  let query =
    match ou with
    | Over ->
        let prop = smart_implies cty1.phi cty2.phi in
        List.fold_right smart_dependent_forall overctx_with_v prop
    | Under ->
        let rhs = List.fold_right smart_dependent_exists underctx cty1.phi in
        let prop = smart_implies cty2.phi rhs in
        List.fold_right smart_dependent_forall overctx_with_v prop
  in
  let () = Statistic.stat_query_formula (rctx.task_name, query) in
  let time, res =
    clock (fun () ->
        let () =
          TypecheckerLog.auxtyping @@ fun _ ->
          Printf.printf "before simp:\n%s\n\n" (layout_prop query)
        in
        let query = SimplProp.simpl_query query in
        let () = Statistic.stat_query_formula (rctx.task_name, query) in
        let () =
          TypecheckerLog.auxtyping @@ fun _ ->
          Printf.printf "check valid:\n%s\n\n" (layout_prop query)
        in
        let () =
          TypecheckerLog.auxtyping @@ fun _ ->
          Printf.printf "let[@valid] tmp = %s\n" (layout_prop_source query)
        in
        (* [Prover.check_valid] decides the negation, built by [smart_not]. *)
        dump_query (smart_not query);
        Prover.check_valid_bool [%here] query ~coerce_to:false)
  in
  let () = Statistic.stat_query_time (rctx.task_name, time) in
  res

(* NOTE: after exists the constraints into the return type, the emptiness can be checked final stage;
   It may cause the more branch analysis.
*)
let lazy_emptiness_check = false

let non_emptiness_cty rctx cty =
  if lazy_emptiness_check then true
  else
    let overctx, underctx = build_wf_ctx (Typectx.ctx_to_list rctx.rty_ctx) in
    let underctx = underctx @ [ (default_v, mk_top_cty cty.nty) ] in
    let () =
      TypecheckerLog.auxtyping @@ fun _ ->
      let overctx =
        List.map (fun (x, cty) -> x#:(RtyBase { ou = Over; cty })) overctx
      in
      let underctx =
        List.map (fun (x, cty) -> x#:(RtyBase { ou = Under; cty })) underctx
      in
      let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
      Typectx.pprint_ctx layout_rty ctx';
      print_newline ()
    in
    let () =
      _assert [%here]
        "left-hand-side type should be closed under over + under ctx"
        (is_close_cty (List.map fst (overctx @ underctx)) cty)
    in
    let query =
      List.fold_right smart_dependent_exists (overctx @ underctx) cty.phi
    in
    let () = Statistic.stat_query_formula (rctx.task_name, query) in
    let time, res =
      clock (fun () ->
          let () =
            TypecheckerLog.auxtyping @@ fun _ ->
            Printf.printf "check sat: %s\n" (layout_prop_ query)
          in
          let () =
            TypecheckerLog.auxtyping @@ fun _ ->
            Printf.printf "let[@sat] tmp = %s\n" (layout_prop_source query)
          in
          dump_query query;
          Prover.check_sat_bool [%here] query ~coerce_to:true)
    in
    let () = Statistic.stat_query_time (rctx.task_name, time) in
    res
