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
  (* let query = fresh_name_prop query in *)
  (* Exists { qv = x#:nty; body = smart_add_to phi query } *)
  smart_exists_phi (x#:nty, phi) query

let report_unclosed loc query =
  let fvs = fv_prop query in
  _assert loc
    (spf "the cty query has free variables %s"
       (List.split_by_comma
          (function { x; ty } -> spf "%s:%s" x (Nt.layout ty))
          fvs))
    (0 == List.length fvs)

let dump_dir = Sys.getenv_opt "POIROT_SMT_DUMP"
let dump_count = ref 0

(* [Prover.check_sat] asserts the axioms, the query, then the axioms again, so
   the answering solver holds each axiom twice. Z3 hash-conses within a context,
   so an assertion is the axiom whose stored encoding it equals. *)
let dump_query () =
  match dump_dir with
  | None -> ()
  | Some dir ->
      let Prover.{ ctx; solver; ax_sys; _ } = Prover.get_prover () in
      let assertions =
        List.slow_rm_dup Z3.Expr.equal @@ Z3.Solver.get_assertions solver
      in
      let names =
        List.map
          (fun e ->
            List.find_map
              (fun (name, ax) ->
                if Z3.Expr.equal e ax.z3_prop then Some name else None)
              (StrMap.to_kv_list ax_sys))
          assertions
      in
      let unnamed = List.length @@ List.filter Option.is_none names in
      _assert [%here] (spf "%i assertions are not axioms" unnamed) (1 = unnamed);
      (* Z3 will not read back the answering solver's [model-add] commands. *)
      let printable = Z3.Solver.mk_solver ctx None in
      Z3.Solver.add printable assertions;
      incr dump_count;
      let write suffix contents =
        Core.Out_channel.write_all
          (spf "%s/q%03i%s" dir !dump_count suffix)
          ~data:contents
      in
      write ".smt2"
      @@ spf "(set-option :timeout %i)\n%s(check-sat)\n"
           (ZUtilsConfig.get_prover_timeout_bound ())
           (Z3.Solver.to_string printable);
      write ".axioms"
      @@ List.split_by "\n" (function Some n -> n | None -> "(query)") names

let check_valid query =
  let () =
    ZUtilsLog.debug @@ fun _ ->
    Printf.printf "check valid: %s\n" (layout_prop_ query)
  in
  let () = report_unclosed [%here] query in
  let res = Prover.check_valid query in
  dump_query ();
  res

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
  let overctx = (default_v, mk_top_cty nty) :: overctx in
  let query =
    match ou with
    | Over ->
        let prop = smart_implies cty1.phi cty2.phi in
        List.fold_right smart_dependent_forall
          (overctx @ [ (default_v, mk_top_cty cty1.nty) ])
          prop
    | Under ->
        let rhs = List.fold_right smart_dependent_exists underctx cty1.phi in
        let prop = smart_implies cty2.phi rhs in
        List.fold_right smart_dependent_forall
          (overctx @ [ (default_v, mk_top_cty cty2.nty) ])
          prop
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
          Printf.printf "let[@axiom] tmp = %s\n" (layout_prop__raw query)
        in
        check_valid query)
  in
  let () = Statistic.stat_query_time (rctx.task_name, time) in
  (* let () = if not res then _die [%here] in *)
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
    let overctx = (default_v, mk_top_cty cty.nty) :: overctx in
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
            Printf.printf "let[@axiom] tmp = %s\n" (layout_prop__raw query)
          in
          let res = Prover.check_sat query in
          dump_query ();
          res)
    in
    let () = Statistic.stat_query_time (rctx.task_name, time) in
    let res =
      match res with SmtUnsat -> false | SmtSat _ -> true | Timeout -> true
      (* NOTE: we cannot decide if this control flow is unreachable, thus continue *)
    in
    (* let () = if List.length underctx > 1 then _die [%here] in *)
    (* let () = if not res then _die [%here] in *)
    res
