module Comparse.Tactic.GenerateIsWellFormedLemma

open Comparse.Bytes.Typeclass
open Comparse.Parser
open Comparse.Tactic.Utils
open FStar.Tactics

val mk_lemma_type_ensures: GenerateParser.bytes_impl -> term -> term -> term -> list ctor -> Tac term
let mk_lemma_type_ensures bi ps_term pre_term x_term ctors =
  let ctor_to_branch (c:ctor): Tac branch =
    let (ctor_name, ctor_type) = c in
    let binders, _ = collect_arr_bs ctor_type in
    let branch_pattern =
      Pat_Cons (pack_fv ctor_name) None (
        Tactics.Util.map (fun b ->
          let (b_bv, (q, _)) = inspect_binder b in
          (Pat_Var b_bv, not (Q_Explicit? q))
        ) binders
      )
    in
    let branch_term =
      Tactics.Util.fold_right (fun b acc ->
        let (ps_b, _) = GenerateParser.parser_from_binder bi b in
        (`(is_well_formed_partial (`#ps_b) (`#pre_term) (`#(binder_to_term b)) /\ (`#acc)))
      ) binders (`True)
    in
    (branch_pattern, branch_term)
  in
  let lhs = `(is_well_formed_partial (`#ps_term) (`#pre_term) (`#x_term)) in
  let rhs = pack (Tv_Match x_term None (Tactics.Util.map ctor_to_branch ctors)) in
  `((`#lhs) <==> (`#rhs))

val mk_lemma_type_smtpat: term -> term -> term -> Tac term
let mk_lemma_type_smtpat ps_term pre_term x_term =
  `(is_well_formed_partial (`#ps_term) (`#pre_term) (`#x_term))

val mk_lemma_type: term -> list binder -> list ctor -> Tac term
let mk_lemma_type type_unapplied params ctors =
  let type_fv =
    match inspect type_unapplied with
    | Tv_FVar fv -> fv
    | _ -> fail ("mk_lemma_type: type_unapplied is not a fv: " ^ term_to_string type_unapplied)
  in
  let type_applied = apply_binders type_unapplied params in
  let (bi, parser_params) = GenerateParser.get_bytes_impl_and_parser_params params in
  let (bytes_term, bytes_like_term) = bi in
  let (ps_term, _) = GenerateParser.parser_from_type bi type_applied in
  let pre_bv = fresh_bv_named "pre" (`bytes_compatible_pre (`#bytes_term) #(`#bytes_like_term)) in
  let pre_term = pack (Tv_Var pre_bv) in
  let x_bv = fresh_bv_named "x" type_applied in
  let x_term = pack (Tv_Var x_bv) in
  let lemma_requires = (`True) in
  let lemma_ensures = mk_lemma_type_ensures bi ps_term pre_term x_term ctors in
  let lemma_smtpat = mk_lemma_type_smtpat ps_term pre_term x_term in
  let eff = pack_comp (C_Lemma lemma_requires (`(fun () -> (`#lemma_ensures))) (`([smt_pat (`#lemma_smtpat)]))) in
  mk_arr (parser_params @ [mk_binder pre_bv; mk_binder x_bv]) eff

val apply_propositional_extensionality: p1:prop -> p2:prop -> squash (p1 <==> p2) -> squash (p1 == p2)
let apply_propositional_extensionality p1 p2 _ = FStar.PropositionalExtensionality.apply p1 p2

val my_isomorphism_is_well_formed_with_id:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_unit bytes a ->
  a_to_b:(a -> b) -> b_to_a:(b -> a) ->
  a_to_b_to_a:(x:a -> squash (b_to_a (a_to_b x) == x)) ->
  b_to_a_to_b:(x:b -> squash (a_to_b (b_to_a x) == x)) ->
  pre:bytes_compatible_pre bytes -> xb:b ->
  squash
  (is_well_formed_partial (isomorphism ps_a ({a_to_b = id a_to_b; b_to_a = id b_to_a; a_to_b_to_a; b_to_a_to_b})) pre xb <==> is_well_formed_partial ps_a pre (b_to_a xb))
let my_isomorphism_is_well_formed_with_id #bytes #bl #a #b ps_a a_to_b b_to_a a_to_b_to_a b_to_a_to_b pre xb = ()

val my_isomorphism_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_unit bytes a ->
  a_to_b:(a -> b) -> b_to_a:(b -> a) ->
  a_to_b_to_a:(x:a -> squash (b_to_a (a_to_b x) == x)) ->
  b_to_a_to_b:(x:b -> squash (a_to_b (b_to_a x) == x)) ->
  pre:bytes_compatible_pre bytes -> xb:b ->
  squash
  (is_well_formed_partial (isomorphism ps_a ({a_to_b; b_to_a; a_to_b_to_a; b_to_a_to_b})) pre xb <==> is_well_formed_partial ps_a pre (b_to_a xb))
let my_isomorphism_is_well_formed #bytes #bl #a #b ps_a a_to_b b_to_a a_to_b_to_a b_to_a_to_b pre xb = ()

val simplify_and_eq_lemma: p1:prop -> p2:prop -> squash p1 -> squash (p1 /\ p2 <==> p2)
let simplify_and_eq_lemma p1 p2 _ = ()

val simplify_is_well_formed_lemma: unit -> Tac unit
let simplify_is_well_formed_lemma () =
  if lax_on() then
    smt ()
  else (
    //Remove garbage from environment
    Tactics.Util.iter (fun b ->
      try clear b
      with _ -> ()
    ) (binders_of_env (cur_env()));

    //Retrieve the parser and value to unfold / destruct
    let (ps_term, x_term) =
      match inspect (cur_goal()) with
      | Tv_App hd (p, Q_Explicit) -> (
        guard (hd `term_eq` (`squash));
        match collect_app p with
        | (eq_term, [lhs, Q_Explicit; rhs, Q_Explicit]) -> (
          guard (eq_term `term_eq` (`(<==>)));
          let (is_well_formed_term, args) = collect_app lhs in
          guard (List.Tot.length args = 6);
          guard (is_well_formed_term `term_eq` (`is_well_formed_partial));
          (fst (List.Tot.index args 3), fst (List.Tot.index args 5))
        )
        | _ -> fail "goal is not an equiv?"
      )
      | _ -> fail "goal is not a app?"
    in

    let ps_qn =
      let (ps_fv, _) = collect_app ps_term in
      implode_qn (get_name_from_fv ps_fv)
    in

    norm [delta_only [ps_qn]];
    let ctrl_with (what:term) (t:term): Tac (bool & ctrl_flag) =
      let (hd, args) = collect_app t in
      if hd `term_eq` (`is_well_formed_partial) && List.Tot.length args = 6 then (
        let ps_term = List.Tot.index args 3 in
        let (ps_unapplied_term, _) = collect_app (fst ps_term) in
        (ps_unapplied_term `term_eq` what, Continue)
      ) else (
        (false, Continue)
      )
    in
    let rw_with_lemma (t:term) (): Tac unit =
      try (
        apply (`apply_propositional_extensionality);
        apply_lemma t
      ) with _ -> trefl()
    in

    ctrl_rewrite TopDown (ctrl_with (`isomorphism)) (rw_with_lemma (`my_isomorphism_is_well_formed_with_id));
    ctrl_rewrite TopDown (ctrl_with (`isomorphism)) (rw_with_lemma (`my_isomorphism_is_well_formed));

    destruct x_term;
    iterAll (fun () ->
      let destruct_binders = intros() in
      let breq_term = binder_to_term (last destruct_binders) in
      l_to_r_breq [breq_term];
      ctrl_rewrite TopDown (ctrl_with (`bind)) (rw_with_lemma (`bind_is_well_formed));
      ctrl_rewrite TopDown (ctrl_with (`refine)) (rw_with_lemma (`refine_is_well_formed));
      norm [simplify; iota];
      (try apply (`simplify_and_eq_lemma) with _ -> ())
    );
    // The last goals should only be about tags being valid,
    // which the SMT can handle easily if their `is_well_formed` lemmas were generated.
    // dump "end goal";
    gather_or_solve_explicit_guards_for_resolved_goals ()
  )

val mk_lemma_val: term -> Tac term
let mk_lemma_val lemma_type =
  let (lemma_binders, lemma_comp) = collect_arr_bs lemma_type in
  let prop =
    match inspect_comp lemma_comp with
    | C_Lemma _ ens _ -> (
      match inspect ens with
      | Tv_Abs _ p -> p
      | _ -> fail "mk_lemma_val: ensures is not a lambda?"
    )
    | _ -> fail "mk_lemma_val: lemma type is not a Lemma?"
  in
  let x = last (lemma_binders) in
  mk_abs lemma_binders (`(assert (`#prop) by (simplify_is_well_formed_lemma ())))

val gen_is_well_formed_lemma_def: term -> Tac (typ & term)
let gen_is_well_formed_lemma_def type_fv =
  let env = top_env () in
  let type_name = get_name_from_fv type_fv in
  let type_declaration =
  match lookup_typ env type_name with
  | Some x -> x
  | None -> fail "Type not found?"
  in
  match inspect_sigelt type_declaration with
  | Sg_Inductive name [] params typ constructors -> (
    let lemma_type = mk_lemma_type type_fv params constructors in
    let lemma_val = mk_lemma_val lemma_type in
    (lemma_type,  lemma_val)
  )
  | Sg_Inductive _ _ _ _ _ -> fail "gen_is_well_formed_lemma_def: higher order types are not supported"
  | _ -> fail "gen_is_well_formed_lemma_def: only inductives are supported"

val gen_is_well_formed_lemma: term -> Tac decls
let gen_is_well_formed_lemma type_fv =
  let type_name = get_name_from_fv type_fv in
  let lemma_name = List.Tot.snoc (moduleof (top_env ()), "ps_" ^ (last type_name) ^ "_is_well_formed") in
  let (lemma_type, lemma_val) = gen_is_well_formed_lemma_def type_fv in
  //dump (term_to_string lemma_type);
  let lemma_letbinding = pack_lb ({
    lb_fv = pack_fv lemma_name;
    lb_us = [];
    lb_typ = lemma_type;
    lb_def = lemma_val;
  }) in
  [pack_sigelt (Sg_Let false [lemma_letbinding])]
