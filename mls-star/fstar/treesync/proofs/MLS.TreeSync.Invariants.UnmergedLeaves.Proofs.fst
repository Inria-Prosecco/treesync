module MLS.TreeSync.Invariants.UnmergedLeaves.Proofs

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.ParentHash
open MLS.TreeCommon
open MLS.TreeCommon.Lemmas
open MLS.MiscLemmas

#set-options "--fuel 1 --ifuel 1"

(*** Create ***)

val unmerged_leaves_ok_tree_create:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  ln:leaf_node_nt bytes tkt ->
  Lemma
  (unmerged_leaves_ok (tree_create (Some ln)))
let unmerged_leaves_ok_tree_create #bytes #bl #tkt ln = ()

(*** Update/Remove ***)

val unmerged_leaves_ok_tree_change_path:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> oln:option (leaf_node_nt bytes tkt) ->
  Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_change_path t li oln None))
let rec unmerged_leaves_ok_tree_change_path #l #i t li oln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li then
      unmerged_leaves_ok_tree_change_path left li oln
    else
      unmerged_leaves_ok_tree_change_path right li oln

val unmerged_leaves_ok_tree_update:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_update t li ln))
let unmerged_leaves_ok_tree_update #l #i t li ln =
  unmerged_leaves_ok_tree_change_path t li (Some ln)

val unmerged_leaves_ok_tree_remove:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_remove t li))
let unmerged_leaves_ok_tree_remove #l #i t li =
  unmerged_leaves_ok_tree_change_path t li None

val unmerged_leaves_ok_mk_blank_tree:
  #bytes:Type0 -> {|bl:bytes_like bytes|} -> #tkt:treekem_types bytes ->
  l:nat -> i:tree_index l ->
  Lemma
  (ensures unmerged_leaves_ok #bytes #bl #tkt (mk_blank_tree l i))
let rec unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt l i =
  if l = 0 then ()
  else (
    unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt (l-1) (left_index i);
    unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt (l-1) (right_index i)
  )

(*** Extend / Truncate ***)

val unmerged_leaves_ok_tree_extend:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  t:treesync bytes tkt l 0 ->
  Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_extend t))
let unmerged_leaves_ok_tree_extend #bytes #bl #tkt #l t =
  unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt l (right_index #(l+1) 0)

val unmerged_leaves_ok_tree_truncate:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:pos ->
  t:treesync bytes tkt l 0{is_tree_empty (TNode?.right t)} ->
  Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_truncate t))
let unmerged_leaves_ok_tree_truncate #bytes #bl #tkt #l t =
  ()

(*** Add ***)

#push-options "--ifuel 2 --fuel 2"
val unmerged_leaves_sorted_insert_sorted:
  x:nat_lbytes 4 ->
  l:list (nat_lbytes 4) ->
  Lemma
  (requires unmerged_leaves_sorted l)
  (ensures unmerged_leaves_sorted (insert_sorted x l))
let rec unmerged_leaves_sorted_insert_sorted x l =
  match l with
  | [] -> ()
  | [y] -> ()
  | y::z::t ->
    if x < y then ()
    else if x = y then ()
    else unmerged_leaves_sorted_insert_sorted x (z::t)
#pop-options

val leaf_at_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> content:leaf_node_nt bytes tkt -> li':leaf_index l i ->
  Lemma
  (requires tree_add_pre t li)
  (ensures leaf_at (tree_add t li content) li' == (if li = li' then Some content else leaf_at t li'))
let rec leaf_at_tree_add #bytes #bl #tkt #l #i t li content li' =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li && is_left_leaf li' then
      leaf_at_tree_add left li content li'
    else if not (is_left_leaf li) && not (is_left_leaf li') then
      leaf_at_tree_add right li content li'
    else ()

val unmerged_leaf_consistent_not_in_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:nat_lbytes 4{~(leaf_index_inside l i li)} ->
  Lemma (unmerged_leaf_consistent t li)
let rec unmerged_leaf_consistent_not_in_tree #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    unmerged_leaf_consistent_not_in_tree left li;
    unmerged_leaf_consistent_not_in_tree right li

val unmerged_leaf_consistent_tree_add_self:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i{li < pow2 32} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires tree_add_pre t li)
  (ensures unmerged_leaf_consistent (tree_add t li content) li)
let rec unmerged_leaf_consistent_tree_add_self #bytes #bl #tkt #l #i t li content =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right ->
    if is_left_leaf li then (
      unmerged_leaf_consistent_tree_add_self left li content;
      unmerged_leaf_consistent_not_in_tree right li
    ) else (
      unmerged_leaf_consistent_not_in_tree left li;
      unmerged_leaf_consistent_tree_add_self right li content
    );
    match opt_content with
    | None -> ()
    | Some content -> mem_insert_sorted li content.unmerged_leaves li

val unmerged_leaf_consistent_tree_add_other:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> content:leaf_node_nt bytes tkt -> li':nat_lbytes 4 ->
  Lemma
  (requires tree_add_pre t li /\ unmerged_leaf_consistent t li')
  (ensures unmerged_leaf_consistent (tree_add t li content) li')
let rec unmerged_leaf_consistent_tree_add_other #bytes #bl #tkt #l #i t li content li' =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right ->
    if is_left_leaf li then (
      unmerged_leaf_consistent_tree_add_other left li content li'
    ) else (
      unmerged_leaf_consistent_tree_add_other right li content li'
    );
    match opt_content with
    | None -> ()
    | Some content -> mem_insert_sorted li content.unmerged_leaves li'

val unmerged_leaves_ok_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires tree_add_pre t li /\ unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_add t li content))
let rec unmerged_leaves_ok_tree_add #bytes #bl #tkt #l #i t li content =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right -> (
    (if is_left_leaf li then unmerged_leaves_ok_tree_add left li content else unmerged_leaves_ok_tree_add right li content);
    match opt_content with
    | None -> ()
    | Some cont -> (
      unmerged_leaf_consistent_tree_add_self t li content;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (unmerged_leaf_consistent_tree_add_other t li content));
      list_for_all_eq (unmerged_leaf_consistent t) cont.unmerged_leaves;
      list_for_all_eq (unmerged_leaf_consistent (tree_add t li content)) (insert_sorted li cont.unmerged_leaves);
      list_for_all_eq (unmerged_leaf_exists t) cont.unmerged_leaves;
      list_for_all_eq (unmerged_leaf_exists (tree_add t li content)) (insert_sorted li cont.unmerged_leaves);
      FStar.Classical.forall_intro (mem_insert_sorted li cont.unmerged_leaves);
      unmerged_leaves_sorted_insert_sorted li cont.unmerged_leaves;
      introduce forall x. List.Tot.mem x (insert_sorted li cont.unmerged_leaves) ==> Some? (leaf_at (tree_add t li content) x)
      with (
        leaf_at_tree_add t li content x
      )
    )
  )

(*** Apply path ***)

val unmerged_leaves_ok_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires apply_path_aux_pre #bytes t p (length #bytes parent_parent_hash) /\ unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (apply_path_aux t p parent_parent_hash))
let rec unmerged_leaves_ok_apply_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf ext_content -> ()
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then
      unmerged_leaves_ok_apply_path_aux left p_next new_parent_parent_hash
    else
      unmerged_leaves_ok_apply_path_aux right p_next new_parent_parent_hash

val unmerged_leaves_ok_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Lemma
  (requires apply_path_pre #bytes t p /\ unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (apply_path t p))
let unmerged_leaves_ok_apply_path #bytes #cb #tkt #l #li t p =
  unmerged_leaves_ok_apply_path_aux t p (root_parent_hash #bytes)

