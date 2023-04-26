module Comparse.Tactic.Utils

open FStar.Tactics

val last: #a:Type0 -> list a -> Tac a
let last l =
  guard (Cons? l);
  List.Tot.last l

//TODO: common
val get_name_from_fv: term -> Tac name
let get_name_from_fv term_fv =
  match inspect term_fv with
  | Tv_FVar fv -> (inspect_fv fv)
  | _ -> fail "type_fv is not a free variable"

val apply_binder: term -> binder -> Tac term
let apply_binder t b =
  let (_, (q, _)) = inspect_binder b in
  let real_q =
    match q with
    | Q_Meta _ -> Q_Implicit
    | x -> x
  in
  pack (Tv_App t (binder_to_term b, real_q))

val apply_binders: term -> list binder -> Tac term
let rec apply_binders t bs =
  match bs with
  | [] -> t
  | bs_head::bs_tail -> apply_binders (apply_binder t bs_head) bs_tail

val term_to_fv: term -> Tac (option fv)
let term_to_fv t =
  match inspect t with
  | Tv_FVar fv -> Some fv
  | Tv_UInst fv _ -> Some fv
  | _ -> None

val term_fv_eq: term -> term -> Tac bool
let term_fv_eq t1 t2 =
  match term_to_fv t1, term_to_fv t2 with
  | Some fv1, Some fv2 -> term_eq (pack (Tv_FVar fv1)) (pack (Tv_FVar fv2)) // inspect_fv fv1 = inspect_fv fv2
  | _, _ -> false

// `l_to_r` is so slow!
val l_to_r_breq: list term -> Tac unit
let l_to_r_breq l =
  let squashed_equality =
    match l with
    | [x] -> x
    | _ -> fail ""
  in
  let squashed_equality_ty = (tc (cur_env ()) squashed_equality) in
  let x_term =
    match inspect squashed_equality_ty with
    | Tv_App squash_term (equality_term, Q_Explicit) -> (
      guard (squash_term `term_fv_eq` (`squash));
      let eq2_term, args = collect_app equality_term in
      guard (eq2_term `term_fv_eq` (`eq2));
      guard (List.Tot.length args = 3);
      let [_; (x_term, _); _] = args in
      guard (Tv_Var? (inspect x_term));
      x_term
    )
    | _ -> fail "malformed equality"
  in
  let ctrl (t:term) : Tac (bool & ctrl_flag) =
    let res =
      match inspect t with
      | Tv_Var _ -> t `term_eq` x_term
      | _ -> false
    in
    res, Continue
  in
  let rw () : Tac unit =
    apply_lemma_rw squashed_equality
  in
  ctrl_rewrite BottomUp ctrl rw

// A subtle different variation
val l_to_r_breq_nosquash: list term -> Tac unit
let l_to_r_breq_nosquash l =
  let equality =
    match l with
    | [x] -> x
    | _ -> fail ""
  in
  let equality_ty = (tc (cur_env ()) equality) in
  let x_term =
      let eq2_term, args = collect_app equality_ty in
      guard (eq2_term `term_fv_eq` (`eq2));
      guard (List.Tot.length args = 3);
      let [_; (x_term, _); _] = args in
      guard (Tv_Var? (inspect x_term));
      x_term
  in
  let ctrl (t:term) : Tac (bool & ctrl_flag) =
    let res =
      match inspect t with
      | Tv_Var _ -> t `term_eq` x_term
      | _ -> false
    in
    res, Continue
  in
  let rw () : Tac unit =
    apply (`FStar.Squash.return_squash);
    apply equality
  in
  ctrl_rewrite BottomUp ctrl rw

val foldr1: #a:Type -> (a -> a -> Tac a) -> list a -> Tac a
let rec foldr1 #a f l =
  match l with
  | [] -> fail "foldr1: called on an empty list"
  | [h] -> h
  | h::t -> f h (foldr1 f t)

val map2: #a:Type -> #b:Type -> #c:Type -> f:(a -> b -> Tac c) -> list a -> list b -> Tac (list c)
let rec map2 #a #b #c f la lb =
  match la, lb with
  | [], [] -> []
  | ha::ta, hb::tb ->
    (f ha hb)::(map2 f ta tb)
  | _, _ -> fail "map2: unconsistent length"

val fit_in: #a:Type -> list bool -> list a -> Tac (list (option a))
let rec fit_in #a lbool la =
  match lbool with
  | [] -> []
  | false::tbool -> None::(fit_in tbool la)
  | true::tbool ->
    match la with
    | [] -> fail "fit_in: la too small"
    | ha::ta -> (Some ha)::(fit_in tbool ta)

private
val my_arrow_to_impl: #a:Type0 -> #b:(squash a -> Type0) -> (squash a -> (squash (b ()))) -> (a ==> b ())
let my_arrow_to_impl #a #b f = FStar.Squash.squash_double_arrow (FStar.Squash.return_squash (fun x -> f (FStar.Squash.return_squash x)))

private
val imp_intro_lem : (#a:Type0) -> (#b : (squash a -> Type0)) -> (a -> squash (b ())) -> Lemma (a ==> b ())
let imp_intro_lem #a #b f =
  FStar.Classical.give_witness (my_arrow_to_impl (fun (x:squash a) -> FStar.Squash.bind_squash x f))

let implies_intro () : Tac binder =
  apply_lemma (`imp_intro_lem);
  intro ()
