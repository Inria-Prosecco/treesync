module MLS.Test.FromExt.TreeKEM

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Operations
open MLS.TreeSync.TreeHash
open MLS.TreeKEM.Operations
open MLS.TreeSyncTreeKEMBinder
open MLS.NetworkBinder
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Result
open MLS.StringUtils
open MLS.Utils
open MLS.Crypto

(*
val find_my_index: {|bytes_like bytes|} -> #l:nat -> treesync bytes tkt l 0 -> key_package_nt bytes tkt -> ML (res:nat{res<pow2 l})
let find_my_index #bl #l t kp =
  let my_signature_key = kp.tbs.leaf_node.data.signature_key in
  let test (olp: option (leaf_node_nt bytes tkt)) =
    match olp with
    | None -> false
    | Some lp -> lp.data.signature_key = my_signature_key
  in
  let res = extract_option "couldn't find my_index" (find_first test (get_leaf_list t)) in
  res

val check_treesync: #l:nat -> #i:tree_index l -> {|crypto_bytes bytes|} -> treesync bytes tkt l i -> mls_bytes bytes -> bool
let check_treesync #l #i #cb t group_id =
  MLS.TreeSync.Invariants.UnmergedLeaves.unmerged_leaves_ok t &&
  MLS.TreeSync.Invariants.ParentHash.parent_hash_invariant t &&
  MLS.TreeSync.Invariants.ValidLeaves.valid_leaves_invariant group_id t

#push-options "--z3rlimit 100"
val gen_treekem_output: {|crypto_bytes bytes|} -> treekem_test_input -> ML treekem_test_output
let gen_treekem_output #cb t =
  let group_id: bytes = empty in
  let ratchet_tree = extract_option "bad ratchet tree" ((ps_prefix_to_ps_whole (ps_ratchet_tree_nt _)).parse (hex_string_to_bytes t.ratchet_tree_before)) in
  let add_sender = FStar.UInt32.v t.add_sender in
  let my_leaf_secret = (hex_string_to_bytes t.my_leaf_secret) in
  let my_key_package = extract_option "bad key package" ((ps_prefix_to_ps_whole (ps_key_package_nt _)).parse (hex_string_to_bytes t.my_key_package)) in
  let my_path_secret = (hex_string_to_bytes t.my_path_secret) in
  let update_sender = FStar.UInt32.v t.update_sender in
  let update_path = extract_option "bad update path" ((ps_prefix_to_ps_whole ps_update_path_nt).parse (hex_string_to_bytes t.update_path)) in
  let update_group_context = hex_string_to_bytes t.update_group_context in
  let l = extract_result (ratchet_tree_l ratchet_tree) in
  let ts0 = extract_result (ratchet_tree_to_treesync l 0 ratchet_tree) in
  let ts0_valid = check_treesync ts0 group_id in
  (
    if ts0_valid then ()
    else IO.print_string ("ratchet_tree_before is not validn")
  );
  let my_index = find_my_index ts0 my_key_package in
  let tk0 = extract_result (treesync_to_treekem ts0) in
  if not (my_index <> add_sender) then
    failwith ("new leaf cannot be equal to add_sender: my_index=" ^ nat_to_string my_index ^ " add_sender=" ^ nat_to_string add_sender ^ "\n")
  else if not (add_sender < pow2 l) then
    failwith "add_sender is too big"
  else if not (update_sender < pow2 l) then
    failwith "update_sender is too big"
  else (
    let upk0 = extract_result (mk_init_path tk0 my_index add_sender my_path_secret empty) in
    let tk1 = tree_apply_path tk0 upk0 in
    let ts1 = ts0 in
    let tree_hash_before: bytes = extract_result (if not (tree_hash_pre ts1) then error "invalid TH pre" else  return (tree_hash ts1)) in
    let root_secret_after_add = extract_result (root_secret tk1 my_index my_leaf_secret) in
    let uncompressed_update_path = extract_result (uncompress_update_path update_sender ts1 update_path) in
    let ups1 = update_path_to_treesync uncompressed_update_path in
    let upk1 = extract_result (update_path_to_treekem update_group_context uncompressed_update_path) in
    let ups1_is_valid = path_is_valid group_id ts1 ups1 in
    let _: unit = extract_result (if ups1_is_valid then return () else error "invalid ups1") in
    let ts2: treesync bytes tkt l 0 = extract_result (if not (apply_path_pre ts1 ups1) then error "invalid pre" else return (apply_path ts1 ups1)) in
    let tk2 = tree_apply_path tk1 upk1 in

    let root_secret_after_update = extract_result (root_secret tk2 my_index my_leaf_secret) in

    let ratchet_tree2 = extract_result (treesync_to_ratchet_tree ts2) in
    let byte_length_ratchet_tree2 = bytes_length (ps_option (ps_node_nt _)) ratchet_tree2 in
    let ratchet_tree_after = if 1 <= byte_length_ratchet_tree2 && byte_length_ratchet_tree2 < pow2 30 then (ps_prefix_to_ps_whole (ps_ratchet_tree_nt _)).serialize ratchet_tree2 else empty in
    let tree_hash_after = extract_result (if not (tree_hash_pre ts2) then error "invalid TH pre 2" else return (tree_hash ts2)) in
    {
      tree_hash_before = bytes_to_hex_string tree_hash_before;
      root_secret_after_add = bytes_to_hex_string root_secret_after_add;
      root_secret_after_update = bytes_to_hex_string root_secret_after_update;
      ratchet_tree_after = bytes_to_hex_string ratchet_tree_after;
      tree_hash_after = bytes_to_hex_string tree_hash_after;
    }
  )
#pop-options

val test_treekem_one: treekem_test -> ML bool
let test_treekem_one t =
  if FStar.UInt16.v t.cipher_suite <> 3 then (
    IO.print_string "Skipping test because only Chacha20Poly1305 is supported\n";
    true
  ) else
  match uint16_to_ciphersuite t.cipher_suite with
  | ProtocolError s -> begin
    IO.print_string ("Skipping one test because of missing ciphersuite: '" ^ s ^ "'\n");
    true
  end
  | InternalError s -> begin
    IO.print_string ("Internal error! '" ^ s ^ "'\n");
    false
  end
  | Success cs -> begin
    let cb = mk_concrete_crypto_bytes cs in
    let sanitize_hash h = if String.length h = 66 then String.sub h 2 64 else h in
    let input = {t.input with
      my_leaf_secret = sanitize_hash t.input.my_leaf_secret;
      my_path_secret = sanitize_hash t.input.my_path_secret;
    } in
    let output = {t.output with
      root_secret_after_add = sanitize_hash t.output.root_secret_after_add;
      root_secret_after_update = sanitize_hash t.output.root_secret_after_update;
    } in
    let t = {t with
      input = input;
      output = output;
    } in
    let our_output = gen_treekem_output #cb t.input in
    let tree_hash_before_ok = check_equal "tree_hash_before_ok" bytes_to_hex_string (hex_string_to_bytes t.output.tree_hash_before) (hex_string_to_bytes our_output.tree_hash_before) in
    let root_secret_after_add_ok = check_equal "root_secret_after_add" bytes_to_hex_string (hex_string_to_bytes t.output.root_secret_after_add) (hex_string_to_bytes our_output.root_secret_after_add) in
    let root_secret_after_update_ok = check_equal "root_secret_after_update" bytes_to_hex_string (hex_string_to_bytes t.output.root_secret_after_update) (hex_string_to_bytes our_output.root_secret_after_update) in
    let ratchet_tree_after_ok = check_equal "ratchet_tree_after" bytes_to_hex_string (hex_string_to_bytes t.output.ratchet_tree_after) (hex_string_to_bytes our_output.ratchet_tree_after) in
    let tree_hash_after_ok = check_equal "tree_hash_after" bytes_to_hex_string (hex_string_to_bytes t.output.tree_hash_after) (hex_string_to_bytes our_output.tree_hash_after) in
    tree_hash_before_ok && root_secret_after_add_ok && root_secret_after_update_ok && ratchet_tree_after_ok && tree_hash_after_ok
  end
*)

val test_treekem: list treekem_test -> ML nat
let test_treekem =
  //test_list "TreeKEM" test_treekem_one
  fun _ -> 0
