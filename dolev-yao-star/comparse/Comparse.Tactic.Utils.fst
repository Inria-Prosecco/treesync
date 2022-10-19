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
      guard (squash_term `term_eq` (`squash));
      let eq2_term, args = collect_app equality_term in
      guard (eq2_term `term_eq` (`eq2));
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
