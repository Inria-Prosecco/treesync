module Comparse.Tactic.GenerateParser

open FStar.Tactics
open Comparse.Bytes.Typeclass
open Comparse.Parser
open Comparse.Tactic.Attributes
open Comparse.Tactic.Utils

(*** Handle annotations in binders ***)

val find_annotation_in_list: list term -> term -> Tac (option (list term))
let rec find_annotation_in_list l expected_hd =
  match l with
  | [] -> None
  | h::t -> (
    let (head, args) = collect_app h in
    if term_eq head expected_hd then (
      Some (List.Tot.map (fun (x, _) -> x) args)
    ) else (
      find_annotation_in_list t expected_hd
    )
  )

val find_annotation_in_binder: binder -> term -> Tac (option (list term))
let find_annotation_in_binder b expected_hd =
  let _, (_, annotations) = inspect_binder b in
  find_annotation_in_list annotations expected_hd

(*** Handle `is_parser` attribute ***)

val find_parser_for: fv -> Tac (option term)
let find_parser_for type_fv =
  let type_qn = implode_qn (inspect_fv type_fv) in
  let candidates = lookup_attr (`is_parser) (top_env ()) in
  let result_fv = Tactics.Util.tryPick (fun parser_fv ->
    match lookup_typ (top_env ()) (inspect_fv parser_fv) with
    | None -> None
    | Some se -> (
      let attrs = sigelt_attrs se in
      let is_parser_for_attr = Tactics.Util.tryPick (fun attr_term ->
        match inspect attr_term with
        | Tv_App hd (arg, Q_Explicit) -> (
          match inspect arg with
          | Tv_Const (C_String s) ->
            if hd `term_eq` (`is_parser_for) && s = type_qn then
              Some attr_term
            else
              None
          | _ -> None
        )
        | _ -> None
      ) attrs in
      match is_parser_for_attr with
      | Some _ -> Some parser_fv
      | None -> None
    )
  ) candidates in
  match result_fv with
  | None -> None
  | Some x -> Some (pack (Tv_FVar x))

(*** Utility functions ***)

type parser_term = term & typ
type bytes_impl = term & term

val mk_ie_app: term -> list term -> list term -> Tac term
let mk_ie_app t implicits explicits =
  let i t = (t, Q_Implicit) in
  let e t = (t, Q_Explicit) in
  mk_app (mk_app t (List.Tot.map i implicits)) (List.Tot.map e explicits)

val apply_implicit_bytes_impl: term -> bytes_impl -> Tac term
let apply_implicit_bytes_impl t (bytes_term, bytes_like_term) =
  mk_ie_app t [bytes_term; bytes_like_term] []

val parser_term_from_type_fv: fv -> Tac term
let parser_term_from_type_fv type_fv =
  match find_parser_for type_fv with
  | Some result -> result
  | None -> (
    guard (Cons? (inspect_fv type_fv));
    let (type_module, type_name) = List.Tot.unsnoc (inspect_fv type_fv) in
    let parser_name = "ps_" ^ type_name in
    let parser_fullname = (List.Tot.snoc (type_module, parser_name)) in
    pack (Tv_FVar (pack_fv parser_fullname))
  )

// `tc (top_env ()) t` doesn't work with bound variables
// and with splice there is no goal, so no `cur_env ()`
val hacky_get_type: term -> Tac typ
let hacky_get_type t =
  match t with
  | Tv_UInst fv _
  | Tv_FVar fv -> tc (top_env ()) t
  | Tv_Var bv -> type_of_bv bv
  | _ -> fail "hacky_get_type: term is not a bv or a fv"

val extract_bytes_impl: list term -> Tac (option bytes_impl)
let extract_bytes_impl ts =
  match ts with
  | b::bl::_ -> (
    let b_type = hacky_get_type b in
    let bl_type = hacky_get_type bl in
    let b_ok = (b_type `term_eq` (`Type0)) in
    let bl_ok = (bl_type `term_eq` (mk_e_app (`bytes_like) [b])) in
    if b_ok && bl_ok then (
      Some (b, bl)
    ) else (
      None
    )
  )
  | _ -> None

val smart_mk_app_aux: term -> list term -> list binder -> Tac term
let rec smart_mk_app_aux t args binders_to_copy =
  match args, binders_to_copy with
  | [], [] -> t
  | a_hd::a_tl, b_hd::b_tl -> (
    let (_, (q, _)) = inspect_binder b_hd in
    let real_q = (
      match q with
      | Q_Meta _ -> Q_Implicit
      | _ -> q
    )
    in
    smart_mk_app_aux (pack (Tv_App t (a_hd, real_q))) a_tl b_tl
  )
  | _, _ -> fail ""

val smart_mk_app: term -> list term -> Tac term
let smart_mk_app t args =
  let t_signature = tc (top_env ()) t in
  let t_signature_binders, _ = collect_arr_bs t_signature in
  smart_mk_app_aux t args t_signature_binders

val parser_from_type: bytes_impl -> term -> Tac parser_term
let parser_from_type (bytes_term, bytes_like_term) t =
  let my_fail () = fail "parser_from_type: head given by `collect_app` is not a fv? (meta program don't handle parametric types, e.g. `option`)" in
  let type_unapplied, type_args = collect_app t in
  match inspect type_unapplied with
  | Tv_UInst fv _
  | Tv_FVar fv ->
    let parser_unapplied = parser_term_from_type_fv fv in
    let parser_signature = tc (top_env ()) parser_unapplied in
    let expanded_type_args =
      match extract_bytes_impl (List.Tot.map fst type_args) with
      | Some _ -> type_args
      | None -> (bytes_term, Q_Implicit)::(bytes_like_term, Q_Implicit)::type_args
    in
    (smart_mk_app parser_unapplied (List.Tot.map fst expanded_type_args), t)
  | Tv_Var _ -> (
    if t `term_eq` bytes_term then
      //Useful in DY* for porting the examples
      //Not useful in actual protocol meant to be executed
      (mk_ie_app (`ps_bytes) [bytes_term; bytes_like_term] [], t)
    else
      my_fail ()
  )
  | _ -> my_fail ()

irreducible let with_parser (#bytes:Type0) {|bytes_like bytes|} (#a:Type0) (x:parser_serializer_prefix bytes a) = ()

val parser_from_binder: bytes_impl -> binder -> Tac parser_term
let parser_from_binder bi b =
  match find_annotation_in_binder b (`with_parser) with
  | None ->
    parser_from_type bi (type_of_binder b)
  | Some [bytes_term; bytes_like_term; typ; ps_typ] ->
    guard (term_eq typ (type_of_binder b));
    (ps_typ, typ)
  | Some _ -> fail "parser_from_binder: malformed annotation"

val mk_parser_unit: bytes_impl -> Tac parser_term
let mk_parser_unit (bytes_term, bytes_like_term) =
  (mk_ie_app (`ps_unit) [bytes_term; bytes_like_term] [], `unit)

(*** Parser for nested pairs ***)

val mk_parser_pair: bytes_impl -> binder -> parser_term -> parser_term -> Tac parser_term
let mk_parser_pair bi binder_a (ps_a, t_a) (ps_b, t_b) =
  let ps_ab = mk_ie_app (apply_implicit_bytes_impl (`bind) bi) [t_a; pack (Tv_Abs binder_a t_b)] [ps_a; pack (Tv_Abs binder_a ps_b)] in
  let t_ab = mk_e_app (`dtuple2) [t_a; pack (Tv_Abs binder_a t_b)] in
  (ps_ab, t_ab)

val mk_parser_pairs: bytes_impl -> list binder -> Tac parser_term
let rec mk_parser_pairs bi l =
  match l with
  | [] -> mk_parser_unit bi
  | [x] -> parser_from_binder bi x
  | h::t -> (
    let pst_h = parser_from_binder bi h in
    let pst_t = mk_parser_pairs bi t in
    mk_parser_pair bi h pst_h pst_t
  )

(*** Parser for records ***)

val mkdtuple2_fv: unit -> Tac fv
let mkdtuple2_fv () =
  pack_fv (explode_qn (`%Mkdtuple2))

val mk_destruct_pairs: list binder -> Tac (pattern & list bv)
let rec mk_destruct_pairs l =
  match l with
  | [] -> (Pat_Constant C_Unit, [])
  | [h] -> (
    let bv_h = bv_of_binder h in
    (Pat_Var bv_h, [bv_h])
  )
  | h::t -> (
    let bv_h = bv_of_binder h in
    let (pattern_t, bv_t) = mk_destruct_pairs t in
    let pattern = Pat_Cons (mkdtuple2_fv ()) None [(Pat_Var bv_h, false); (pattern_t, false)] in
    let bvs = bv_h::bv_t in
    (pattern, bvs)
  )

val mk_construct_record: name -> list bv -> Tac term
let mk_construct_record constructor_name bvs =
  let constructor_term = (pack (Tv_FVar (pack_fv constructor_name))) in
  let constructor_args = Tactics.Util.map (fun bv -> (pack (Tv_Var bv), Q_Explicit)) bvs in
  mk_app constructor_term constructor_args

val mk_record_isomorphism_f: typ -> name -> list binder -> Tac term
let mk_record_isomorphism_f result_type constructor_name constructor_binders =
  let (match_pattern, bvs) = mk_destruct_pairs constructor_binders in
  let match_body = mk_construct_record constructor_name bvs in
  let x_bv = fresh_bv result_type in
  pack (Tv_Abs (mk_binder x_bv) (pack (Tv_Match (pack (Tv_Var x_bv)) None [(match_pattern, match_body)])))

val mk_construct_pairs: list bv -> Tac term
let rec mk_construct_pairs l =
  match l with
  | [] -> (`())
  | [h] -> pack (Tv_Var h)
  | h::t ->
    mk_e_app (`Mkdtuple2) [pack (Tv_Var h); mk_construct_pairs t]

val mk_record_isomorphism_g: typ -> name -> list binder -> Tac term
let mk_record_isomorphism_g input_type constructor_name constructor_binders =
  let bvs = Tactics.Util.map (fun b -> bv_of_binder b) constructor_binders in
  let match_pattern = Pat_Cons (pack_fv constructor_name) None (List.Tot.map (fun bv -> (Pat_Var bv, false)) bvs) in
  let match_body = mk_construct_pairs bvs in
  let x_bv = fresh_bv input_type in
  pack (Tv_Abs (mk_binder x_bv) (pack (Tv_Match (pack (Tv_Var x_bv)) None [(match_pattern, match_body)])))

val dtuple2_ind: #a:Type -> #b:(a -> Type) -> p:((x:a & b x) -> Type0) -> squash (forall (x:a) (y:b x). p (|x, y|)) -> Lemma (forall xy. p xy)
let dtuple2_ind #a #b p _ = ()

val arrow_to_forall: #a:Type -> p:(a -> Type0) -> squash (forall (x:a). p x) -> (x:a -> squash (p x))
let arrow_to_forall #a p _ x =
  ()

val wrap_isomorphism_proof: (unit -> Tac unit) -> unit -> Tac unit
let wrap_isomorphism_proof tau () =
  apply (`arrow_to_forall);
  if lax_on() then
    smt ()
  else
    tau ()

val prove_record_isomorphism_from_pair: unit -> Tac unit
let prove_record_isomorphism_from_pair () =
  let _ = repeat (fun () ->
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    ()
  ) in
  let _ = forall_intro () in
  trefl();
  gather_or_solve_explicit_guards_for_resolved_goals ()

val prove_record_isomorphism_from_record: unit -> Tac unit
let prove_record_isomorphism_from_record () =
  let b = forall_intro () in
  destruct (binder_to_term b);
  let binders = intros () in
  let breq = last binders in
  l_to_r_breq [binder_to_term breq];
  trefl ();
  gather_or_solve_explicit_guards_for_resolved_goals ()

val mk_record_isomorphism: bytes_impl -> typ -> name -> list binder -> parser_term -> Tac parser_term
let mk_record_isomorphism bi result_type constructor_name constructor_binders (parser_term, parser_type) =
  let the_isomorphism =
    mk_ie_app (`Mkisomorphism_between) [
      parser_type;
      result_type
    ] [
      mk_record_isomorphism_f parser_type constructor_name constructor_binders;
      mk_record_isomorphism_g result_type constructor_name constructor_binders;
      (`(synth_by_tactic (wrap_isomorphism_proof prove_record_isomorphism_from_pair)));
      (`(synth_by_tactic (wrap_isomorphism_proof prove_record_isomorphism_from_record)));
    ]
  in
  let result_parser_term =
    mk_ie_app (apply_implicit_bytes_impl (`isomorphism) bi) [
      parser_type;
      result_type
    ] [
      parser_term;
      the_isomorphism
    ]
  in
  (result_parser_term, result_type)

val mk_record_parser: bytes_impl -> ctor -> typ -> Tac parser_term
let mk_record_parser bi (c_name, c_typ) result_parsed_type =
  let binders, _ = collect_arr_bs c_typ in
  let pairs_parser = mk_parser_pairs bi binders in
  mk_record_isomorphism bi result_parsed_type c_name binders pairs_parser

(*** Parser for sum type ***)

// Annotation
irreducible let with_tag (#a:Type0) (x:a) = ()
// /!\ Don't work as expected, see https://github.com/FStarLang/FStar/issues/2571
// unfold let with_num_tag (n:nat) (x:nat_lbytes n) = with_tag #(nat_lbytes n) x
irreducible let with_num_tag (n:nat) (x:nat_lbytes n) = ()

val get_tag_from_ctor: ctor -> Tac (option (typ & term))
let get_tag_from_ctor (ctor_name, ctor_typ) =
  match lookup_typ (top_env ()) ctor_name with
  | Some sigelt -> (
    let attrs = sigelt_attrs sigelt in
    match find_annotation_in_list attrs (`with_tag) with
    | Some [tag_typ; tag_val] ->
      Some (tag_typ, tag_val)
    | Some _ -> fail "get_tag_from_ctor: malformed annotation"
    | None -> (
      match find_annotation_in_list attrs (`with_num_tag) with
      | Some [tag_sz; tag_val] -> Some (`(nat_lbytes (`#tag_sz)), tag_val)
      | Some _ -> fail "get_tag_from_ctor: malformed annotation"
      | None -> None
    )
  )
  | None -> fail "get_tag_from_ctor: cannot find ctor type?"

let rec find_nbytes (n:nat) (acc:nat): Tac nat =
  if n < pow2 (8 `op_Multiply` acc) then
    acc
  else
    find_nbytes n (acc+1)

val get_tag_from_ctors: list ctor -> Tac (typ & (list term))
let get_tag_from_ctors ctors =
  let opt_tags = Tactics.Util.map get_tag_from_ctor ctors in
  if List.Tot.for_all (Some?) opt_tags then (
    let tags = Tactics.Util.map (fun (opt_tag:option(typ & term)) -> guard (Some? opt_tag); Some?.v opt_tag) opt_tags in
    guard (Cons? tags);
    let tag_typs, tag_vals = List.Tot.unzip tags in
    let tag_typ =
      guard (List.Tot.for_all (fun x -> term_eq x (Cons?.hd tag_typs)) tag_typs);
      Cons?.hd tag_typs
    in
    (tag_typ, tag_vals)
  ) else if List.Tot.for_all (None?) opt_tags then (
    let nbytes = find_nbytes (List.Tot.length ctors) 0 in
    let pack_int i = pack (Tv_Const (C_Int i)) in
    (mk_e_app (`nat_lbytes) [pack_int nbytes], Tactics.Util.mapi (fun i _ -> pack_int i) ctors)
  ) else (
    fail "get_tag_from_ctors: inconsistent tag annotation"
  )

val mk_tag_parser: bytes_impl -> typ -> list term -> Tac parser_term
let mk_tag_parser bi tag_typ tag_vals =
  let pred =
    let tag_bv = fresh_bv tag_typ in
    let tag_term = pack (Tv_Var tag_bv) in
    let mk_equality v1 v2 = mk_ie_app (`op_Equality) [tag_typ] [v1; v2] in
    let mk_disj value acc: Tac term = `(((`#(mk_equality tag_term value))) || (`#acc)) in
    guard (Cons? tag_vals);
    let tag_vals_head::tag_vals_tail = tag_vals in
    let disj = fold_right mk_disj tag_vals_tail (`((`#(mk_equality tag_term tag_vals_head)))) in
    pack (Tv_Abs (mk_binder tag_bv) disj)
  in
  let (tag_parser, tag_typ) = parser_from_type bi tag_typ in
  (mk_ie_app (apply_implicit_bytes_impl (`refine) bi) [tag_typ] [tag_parser; pred], mk_e_app (`refined) [tag_typ; pred])

val term_to_pattern: term -> Tac pattern
let rec term_to_pattern t =
  let (hd, args) = collect_app t in
  let args_pat = Tactics.Util.map (fun (arg, q) -> (term_to_pattern arg, not (Q_Explicit? q))) args in
  match inspect hd with
  | Tv_UInst fv _
  | Tv_FVar fv ->
    Pat_Cons fv None args_pat
  | Tv_Const c ->
    guard (List.Tot.length args = 0);
    Pat_Constant c
  | _ -> fail ("term_to_pattern: term type not handled (not fv or const). Term: `" ^ term_to_string t ^ "`")

val mk_middle_sum_type_parser: bytes_impl -> parser_term -> list term -> list ctor -> Tac (parser_term & term)
let mk_middle_sum_type_parser bi (tag_parser, tag_typ) tag_vals ctors =
  let pair_parsers =
    Tactics.Util.map
      (fun (ctor_name, ctor_typ) ->
        let binders, _ = collect_arr_bs ctor_typ in
        mk_parser_pairs bi binders
      )
      ctors
  in
  let (tag_to_pair_type_term, tag_to_pair_parser_term) =
    let tag_bv = fresh_bv tag_typ in
    let tag_term = pack (Tv_Var tag_bv) in
    // Should be provable, but a dynamic check is enough
    guard (List.Tot.length tag_vals = List.Tot.length pair_parsers);
    let (branches_typ, branches_term) =
      List.Tot.unzip (
        Tactics.Util.map
          (fun (tag_val, (pair_parser_term, pair_parser_typ)) -> (
            (term_to_pattern tag_val, pair_parser_typ),
            (term_to_pattern tag_val, pair_parser_term)
          ))
          (List.Pure.zip tag_vals pair_parsers)
      )
    in
    (
      pack (Tv_Abs (mk_binder tag_bv) (pack (Tv_Match tag_term None branches_typ))),
      pack (Tv_Abs (mk_binder tag_bv) (pack (Tv_Match tag_term None branches_term)))
    )
  in
  let middle_parser = mk_ie_app (apply_implicit_bytes_impl (`bind) bi) [tag_typ; tag_to_pair_type_term] [tag_parser; tag_to_pair_parser_term] in
  let middle_typ = mk_e_app (`dtuple2) [tag_typ; tag_to_pair_type_term] in
  ((middle_parser, middle_typ), tag_to_pair_type_term)

val mk_middle_to_sum_fun: typ -> term -> list term -> list ctor -> Tac term
let mk_middle_to_sum_fun tag_typ tag_to_pair_typ tag_vals ctors =
  guard (List.Tot.length tag_vals = List.Tot.length ctors);
  let branches =
    Tactics.Util.map
      (fun (tag_val, (ctor_name, ctor_typ)) ->
        let binders, _ = collect_arr_bs ctor_typ in
        let (pair_pattern, bvs) = mk_destruct_pairs binders in
        let rec_term = mk_construct_record ctor_name bvs in
        let bvs = Tactics.Util.map (fun b -> bv_of_binder b) binders in
        let pattern = Pat_Cons (mkdtuple2_fv ()) None [(term_to_pattern tag_val, false); (pair_pattern, false)] in
        (pattern, rec_term)
      )
      (List.Pure.zip tag_vals ctors)
  in
  let pair_bv = fresh_bv (mk_e_app (`dtuple2) [tag_typ; tag_to_pair_typ]) in
  pack (Tv_Abs (mk_binder pair_bv) (pack (Tv_Match (pack (Tv_Var pair_bv)) None branches)))

val mk_sum_to_middle_fun: typ -> list term -> list ctor -> Tac term
let mk_sum_to_middle_fun sum_typ tag_vals ctors =
  guard (List.Tot.length tag_vals = List.Tot.length ctors);
  let branches =
    Tactics.Util.map
      (fun (tag_val, (ctor_name, ctor_typ)) ->
        let (ctor_binders, _) = collect_arr_bs ctor_typ in
        let bvs = Tactics.Util.map (fun b -> bv_of_binder b) ctor_binders in
        let match_pattern = Pat_Cons (pack_fv ctor_name) None (List.Tot.map (fun bv -> (Pat_Var bv, false)) bvs) in
        let pairs_term = mk_construct_pairs bvs in
        let match_body = mk_e_app (`Mkdtuple2) [tag_val; pairs_term] in
        (match_pattern, match_body)
      )
      (List.Pure.zip tag_vals ctors)
  in
  let sum_bv = fresh_bv sum_typ in
  pack (Tv_Abs (mk_binder sum_bv) (pack (Tv_Match (pack (Tv_Var sum_bv)) None branches)))

val refined_ind: a:Type -> pred:(a -> bool) -> p:(refined a pred -> Type0) -> squash (forall (x:a). pred x ==> p x) -> squash (forall (x:refined a pred). p x)
let refined_ind a pred p _ = ()

val or_split: b1:bool -> b2:bool -> (p:(squash (b1 || b2) -> Type0)) -> squash (b1 ==> p ()) -> squash (b2 ==> p ()) -> squash (b1 || b2 ==> p ())
let or_split b1 b2 p _ _ = ()

val eq_to_eq: a:eqtype -> x:a -> y:a -> p:(squash (x == y) -> Type0) -> squash (x == y ==> p ()) -> squash (x = y ==> p ())
let eq_to_eq a x y p _ = ()

//val add_squash: p:Type0 -> q:(squash p -> Type0) -> squash (squash p ==> q ()) -> squash (p ==> q ())
//let add_squash p q _ =
//  introduce p ==> q () with _. ()

val remove_refine: a:Type0 -> p:(a -> Type0) -> q:(a -> Type0) -> squash (forall (x:a). q x) -> squash (forall (x:a{p x}). q x)
let remove_refine a p q _ = ()

val forall_unit_intro: p:(unit -> Type0) -> squash (p ()) -> squash (forall (y:unit). p y)
let forall_unit_intro p _ = ()

val prove_pair_sum_pair_isomorphism: unit -> Tac unit
let prove_pair_sum_pair_isomorphism () =
  apply_lemma (`dtuple2_ind);
  apply (`refined_ind);
  let _ = forall_intro () in
  norm [primops; iota];
  let solve_one_goal () =
    apply (`eq_to_eq);
    let x_eq_term = binder_to_term (implies_intro ()) in
    l_to_r_breq_nosquash [x_eq_term];
    let _ = repeat (fun () ->
      apply_lemma (`dtuple2_ind);
      let _ = forall_intro () in
      ()
    ) in
    (
      try apply (`forall_unit_intro)
      with _ -> let _ = forall_intro () in ()
    );
    trefl()
  in
  let _ = repeat (fun () ->
    apply (`or_split);
    focus solve_one_goal
  ) in
  focus solve_one_goal;
  gather_or_solve_explicit_guards_for_resolved_goals ()

val prove_sum_pair_sum_isomorphism: unit -> Tac unit
let prove_sum_pair_sum_isomorphism () =
  compute();
  let x_term = binder_to_term (forall_intro ()) in
  destruct x_term;
  iterAll (fun () ->
    let destruct_binders = intros() in
    let breq_term = binder_to_term (last destruct_binders) in
    l_to_r_breq [breq_term];
    compute();
    trefl ()
  );
  gather_or_solve_explicit_guards_for_resolved_goals ()

val mk_sum_isomorphism: bytes_impl -> typ -> typ -> term -> list term -> list ctor -> parser_term -> Tac parser_term
let mk_sum_isomorphism bi tag_typ result_typ tag_to_pair_typ tag_vals ctors (pairs_parser, pairs_typ) =
  let middle_to_sum_def = mk_middle_to_sum_fun tag_typ tag_to_pair_typ tag_vals ctors in
  let sum_to_middle_def = mk_sum_to_middle_fun result_typ tag_vals ctors in
  let middle_typ = mk_e_app (`dtuple2) [tag_typ; tag_to_pair_typ] in
  let mk_a_to_b (a:typ) (b:typ) = (pack (Tv_Arrow (fresh_binder a) (pack_comp (C_Total b)))) in
  //We need to help F* with the type of things otherwise it is completely lost
  let ascribe_type (t:typ) (x:term) = mk_ie_app (`id) [t] [x] in
  let the_isomorphism = mk_ie_app (`Mkisomorphism_between) [
    pairs_typ;
    result_typ
  ] [
    ascribe_type (mk_a_to_b middle_typ result_typ) middle_to_sum_def;
    ascribe_type (mk_a_to_b result_typ middle_typ) sum_to_middle_def;
    (`(synth_by_tactic (wrap_isomorphism_proof prove_pair_sum_pair_isomorphism)));
    (`(synth_by_tactic (wrap_isomorphism_proof prove_sum_pair_sum_isomorphism)))
  ] in
  let result_parser = mk_ie_app (apply_implicit_bytes_impl (`isomorphism) bi) [
    pairs_typ;
    result_typ
  ] [
    pairs_parser;
    the_isomorphism
  ] in
  (result_parser, result_typ)

val mk_sum_type_parser: bytes_impl -> list ctor -> typ -> Tac parser_term
let mk_sum_type_parser bi ctors result_type =
  let (tag_typ, tag_vals) = get_tag_from_ctors ctors in
  let tag_parser_term = mk_tag_parser bi tag_typ tag_vals in
  let (tag_parser, tag_typ) = tag_parser_term in
  let (middle_sum_type_parser_term, tag_to_pair_typ) = mk_middle_sum_type_parser bi tag_parser_term tag_vals ctors in
  mk_sum_isomorphism bi tag_typ result_type tag_to_pair_typ tag_vals ctors middle_sum_type_parser_term

(*** Parser for open enum ***)

irreducible let open_tag = ()

val is_open_ctor: ctor -> Tac bool
let is_open_ctor (ctor_name, _) =
  match lookup_typ (top_env ()) ctor_name with
  | Some sigelt -> (
    let attrs = sigelt_attrs sigelt in
    match find_annotation_in_list attrs (`open_tag) with
    | Some [] ->
      true
    | Some _ -> fail "is_open_ctor: malformed annotation"
    | None -> false
  )
  | None -> fail "is_open_ctor: cannot find ctor type?"

val is_closed_ctor: ctor -> Tac bool
let is_closed_ctor c =
  not (is_open_ctor c)

val is_open_enum: list ctor -> Tac bool
let is_open_enum ctors =
  1 <= List.Tot.length (Tactics.Util.filter is_open_ctor ctors)

val get_closed_and_open_ctors: list ctor -> Tac (list ctor & option ctor)
let get_closed_and_open_ctors ctors =
  let closed_ctors = Tactics.Util.filter (fun ctor -> not (is_open_ctor ctor)) ctors in
  let open_ctor =
    match Tactics.Util.filter is_open_ctor ctors with
    | [res] -> Some res
    | [] -> None
    | _ -> fail "get_closed_and_open_ctors: too many open ctor"
  in
  (closed_ctors, open_ctor)

val mk_tag_to_open_enum: typ -> list ctor -> ctor -> Tac term
let mk_tag_to_open_enum tag_typ ctors open_ctor =
  let branches_closed =
    Tactics.Util.map
      (fun ctor ->
        let (ctor_name, _) = ctor in
        let opt_tag = get_tag_from_ctor ctor in
        guard (Some? opt_tag);
        let (tag_typ, tag_val) = Some?.v opt_tag in
        (term_to_pattern tag_val, pack (Tv_FVar (pack_fv ctor_name)))
      )
      ctors
  in
  let branch_open =
    let tag_bv = fresh_bv tag_typ in
    let (open_ctor_name, _) = open_ctor in
    (Pat_Var tag_bv, mk_e_app (pack (Tv_FVar (pack_fv open_ctor_name))) [pack (Tv_Var tag_bv)])
  in
  let branches = branches_closed @ [branch_open] in
  let tag_bv = fresh_bv tag_typ in
  pack (Tv_Abs (mk_binder tag_bv) (pack (Tv_Match (pack (Tv_Var tag_bv)) None branches)))

val mk_open_enum_to_tag: typ -> typ -> list ctor -> ctor -> Tac term
let mk_open_enum_to_tag tag_typ open_enum_typ ctors open_ctor =
  let branches_closed =
    Tactics.Util.map
      (fun ctor ->
        let (ctor_name, _) = ctor in
        let opt_tag = get_tag_from_ctor ctor in
        guard (Some? opt_tag);
        let (tag_typ, tag_val) = Some?.v opt_tag in
        (Pat_Cons (pack_fv ctor_name) None [], tag_val)
      )
      ctors
  in
  let branch_open =
    let tag_bv = fresh_bv tag_typ in
    let (open_ctor_name, _) = open_ctor in
    (Pat_Cons (pack_fv open_ctor_name) None [Pat_Var tag_bv, false], pack (Tv_Var tag_bv))
  in
  let branches = branches_closed @ [branch_open] in
  let x_bv = fresh_bv open_enum_typ in
  pack (Tv_Abs (mk_binder x_bv) (pack (Tv_Match (pack (Tv_Var x_bv)) None branches)))

val mk_open_enum_isomorphism: bytes_impl -> parser_term -> typ -> list ctor -> ctor -> Tac parser_term
let mk_open_enum_isomorphism bi (tag_parser, tag_typ) open_enum_typ ctors open_ctor =
  let tag_to_open_def = mk_tag_to_open_enum tag_typ ctors open_ctor in
  let open_to_tag_def = mk_open_enum_to_tag tag_typ open_enum_typ ctors open_ctor in
  let the_isomorphism =
    mk_ie_app (`Mkisomorphism_between) [
      tag_typ;
      open_enum_typ;
    ] [
      tag_to_open_def;
      open_to_tag_def;
      (`(fun _ -> ())); // Meh do the proof by SMT
      (`(fun _ -> ()));
    ]
  in
  let open_enum_parser = mk_ie_app (apply_implicit_bytes_impl (`isomorphism) bi) [
    tag_typ;
    open_enum_typ;
  ] [
    tag_parser;
    the_isomorphism;
  ] in
  (open_enum_parser, open_enum_typ)

val mk_open_enum_parser: bytes_impl -> list ctor -> typ -> Tac parser_term
let mk_open_enum_parser bi ctors result_typ =
  let (closed_ctors, opt_open_ctor) = get_closed_and_open_ctors ctors in
  guard (Some? opt_open_ctor);
  let Some open_ctor = opt_open_ctor in
  let (tag_typ, _) = get_tag_from_ctors closed_ctors in
  let tag_parser_term = parser_from_type bi tag_typ in
  mk_open_enum_isomorphism bi tag_parser_term result_typ closed_ctors open_ctor

(*** Parser for computed type ***)

val substitute_parser_in_term: bytes_impl -> term -> Tac term
let rec substitute_parser_in_term bi t =
  match inspect t with
  | Tv_Match scrutinee ret branches ->
    let new_branches = Tactics.Util.map
      (fun (pat, br_term) -> (pat, substitute_parser_in_term bi br_term))
      branches
    in
    pack (Tv_Match scrutinee ret new_branches)
  | Tv_Let recf attrs bv def body ->
    pack (Tv_Let recf attrs bv def (substitute_parser_in_term bi body))
  // Remove type ascription because sometimes F* gives us (...) <: Type0
  | Tv_AscribedC e c tac use_eq -> substitute_parser_in_term bi e
  | Tv_AscribedT e t tac use_eq -> substitute_parser_in_term bi e
  | Tv_App _ _
  | Tv_FVar _
  | Tv_UInst _ _ -> (
    fst (parser_from_type bi t)
  )
  | _ -> (
    dump (term_to_string t);
    dump (term_to_ast_string t);
    fail "substitute_parser_in_term: term not handled by the metaprogram"
  )

(*** Parser generator ***)

val get_bytes_impl_and_parser_params: list binder -> Tac (bytes_impl & list binder)
let get_bytes_impl_and_parser_params params =
  let mk_bi_binders (): Tac (binder & binder) =
    let b = pack_binder (fresh_bv_named "bytes" (`Type0)) Q_Implicit [] in
    let bl = pack_binder (fresh_bv_named "bl" (`(bytes_like (`#(binder_to_term b))))) (Q_Meta (`FStar.Tactics.Typeclasses.tcresolve)) [] in
    (b, bl)
  in
  let ((bytes_binder, bytes_like_binder), tail_params) =
    match params with
    | b::bl::tail_params -> (
      let b_ok = ((type_of_binder b) `term_eq` (`Type0)) in
      let bl_ok = ((type_of_binder bl) `term_eq` (mk_e_app (`bytes_like) [binder_to_term b])) in
      let (b_bv, (_, b_annots)) = inspect_binder b in
      let b_implicit = pack_binder b_bv Q_Implicit b_annots in
      if b_ok && bl_ok then (
        ((b_implicit, bl), tail_params)
      ) else (
        (mk_bi_binders (), params)
      )
    )
    | _ -> (mk_bi_binders (), params)
  in
  let bi = (binder_to_term bytes_binder, binder_to_term bytes_like_binder) in
  let parser_params = bytes_binder::bytes_like_binder::tail_params in
  (bi, parser_params)

val is_tagged_type: list ctor -> Tac bool
let is_tagged_type constructors =
  match constructors with
  | [ctor] -> (
    match get_tag_from_ctor ctor with
    | Some _ -> true
    | None ->   false
  )
  | ctors -> (
    true
  )

val gen_parser_fun: term -> term -> Tac (typ & term & bool)
let gen_parser_fun parser_ty type_fv =
  let env = top_env () in
  let type_name = get_name_from_fv type_fv in
  let type_declaration =
    match lookup_typ env type_name with
    | Some x -> x
    | None -> fail "Type not found?"
  in
  let (bi, result_parsed_type, parser_params, parser_fun_body, is_opaque) =
    match inspect_sigelt type_declaration with
    | Sg_Inductive name [] params typ constructors -> (
      guard (term_eq typ (`Type0) || term_eq typ (`eqtype)); //TODO this is a bit hacky
      let (bi, parser_params) = get_bytes_impl_and_parser_params params in
      let result_parsed_type = apply_binders type_fv params in
      let (parser_fun_body, _) =
        if is_tagged_type constructors then (
          if is_open_enum constructors then (
            mk_open_enum_parser bi constructors result_parsed_type
          ) else (
            mk_sum_type_parser bi constructors result_parsed_type
          )
        ) else (
          guard (Cons? constructors);
          mk_record_parser bi (Cons?.hd constructors) result_parsed_type
        )
      in
      (bi, result_parsed_type, parser_params, parser_fun_body, true)
    )
    | Sg_Inductive _ _ _ _ _ -> fail "gen_parser_fun: higher order types are not supported"
    | Sg_Let false [lb] -> (
      let (params, body) = collect_abs (inspect_lb lb).lb_def in
      let (bi, parser_params) = get_bytes_impl_and_parser_params params in
      let result_parsed_type = apply_binders type_fv params in
      let parser_fun_body = substitute_parser_in_term bi body in
      (bi, result_parsed_type, parser_params, parser_fun_body, false)
    )
    | Sg_Let _ _ -> fail "gen_parser_fun: recursive lets are not supported"
    | _ -> fail "gen_parser_fun: only inductives are supported"
  in
  let parser_fun = mk_abs parser_params parser_fun_body in
  let (bytes_term, bytes_like_term) = bi in
  let unparametrized_parser_type = mk_app parser_ty [bytes_term, Q_Explicit; bytes_like_term, Q_Implicit; result_parsed_type, Q_Explicit] in
  let parser_type = mk_arr parser_params (pack_comp (C_Total unparametrized_parser_type)) in
  (parser_type, parser_fun, is_opaque)

val gen_parser_aux: term -> term -> Tac decls
let gen_parser_aux parser_ty type_fv =
  let type_name = get_name_from_fv type_fv in
  let parser_name = List.Tot.snoc (moduleof (top_env ()), "ps_" ^ (last type_name)) in
  let (parser_type, parser_fun, is_opaque) = gen_parser_fun parser_ty type_fv in
  //dump (term_to_string parser_fun);
  //dump (term_to_string parser_type);
  let parser_letbinding = pack_lb ({
    lb_fv = pack_fv parser_name;
    lb_us = [];
    lb_typ = parser_type;
    lb_def = parser_fun;
  }) in
  let sv = pack_sigelt (Sg_Let false [parser_letbinding]) in
  let sv =
    if is_opaque then set_sigelt_attrs [(`"opaque_to_smt")] sv
    else sv
  in
  [sv]

val gen_parser: term -> Tac decls
let gen_parser type_fv =
  gen_parser_aux (`parser_serializer) type_fv

val gen_parser_prefix: term -> Tac decls
let gen_parser_prefix type_fv =
  gen_parser_aux (`parser_serializer_prefix) type_fv
