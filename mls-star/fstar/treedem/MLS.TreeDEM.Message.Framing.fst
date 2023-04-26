module MLS.TreeDEM.Message.Framing

open Comparse
open MLS.TreeDEM.Keys
open MLS.TreeDEM.Message.Content
open MLS.TreeDEM.Message.Transcript
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeDEM.Message.Types
open MLS.Result

module NT = MLS.TreeDEM.NetworkTypes

(*** Authentication ***)

val compute_message_confirmation_tag:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> bytes ->
  result (lbytes bytes (hmac_length #bytes))
let compute_message_confirmation_tag #bytes #cb confirmation_key confirmed_transcript_hash =
  hmac_hmac confirmation_key confirmed_transcript_hash

val knows_group_context:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sender_nt bytes ->
  bool
let knows_group_context #bytes #bl sender = NT.S_member? sender || NT.S_new_member_commit? sender

val compute_tbs:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  wire_format_nt -> content:framed_content_nt bytes -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  framed_content_tbs_nt bytes
let compute_tbs #bytes #bl wire_format content group_context =
  ({
    wire_format;
    content;
    group_context = (match group_context with | Some gc -> gc | None -> ());
  } <: framed_content_tbs_nt bytes)

val compute_tbm:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  content:framed_content_nt bytes -> framed_content_auth_data_nt bytes content.content.content_type -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  authenticated_content_tbm_nt bytes
let compute_tbm #bytes #bl content auth group_context =
  let content_tbs = compute_tbs WF_mls_public_message content group_context in
  ({
    content_tbs;
    auth;
  } <: authenticated_content_tbm_nt bytes)

val compute_message_signature:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sign_private_key bytes -> sign_nonce bytes -> wire_format_nt -> content:framed_content_nt bytes -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  result (sign_signature bytes)
let compute_message_signature #bytes #cb sk rand wire_format msg group_context =
  let tbs = compute_tbs wire_format msg group_context in
  let serialized_tbs: bytes = serialize (framed_content_tbs_nt bytes) tbs in
  if not (length serialized_tbs < pow2 30 && sign_with_label_pre #bytes "FramedContentTBS" (length #bytes serialized_tbs)) then error "compute_message_signature: tbs too long"
  else (
    return (sign_with_label sk "FramedContentTBS" serialized_tbs rand)
  )

val check_message_signature:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sign_public_key bytes -> sign_signature bytes -> wire_format_nt -> content:framed_content_nt bytes -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  result bool
let check_message_signature #bytes #cb pk signature wire_format msg group_context =
  let tbs = compute_tbs wire_format msg group_context in
  let serialized_tbs: bytes = serialize (framed_content_tbs_nt bytes) tbs in
  if not (length serialized_tbs < pow2 30 && sign_with_label_pre #bytes "FramedContentTBS" (length #bytes serialized_tbs)) then error "check_message_signature: tbs too long"
  else (
    return (verify_with_label pk "FramedContentTBS" serialized_tbs signature)
  )

val compute_message_membership_tag:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> content:framed_content_nt bytes -> framed_content_auth_data_nt bytes content.content.content_type -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  result (lbytes bytes (hmac_length #bytes))
let compute_message_membership_tag #bytes #cb membership_key msg auth group_context =
  let tbm = compute_tbm msg auth group_context in
  let serialized_tbm = serialize (authenticated_content_tbm_nt bytes) tbm in
  hmac_hmac membership_key serialized_tbm

val message_compute_auth:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  message_content bytes -> sign_private_key bytes -> sign_nonce bytes -> option (group_context_nt bytes) -> bytes -> bytes ->
  result (message_auth bytes)
let message_compute_auth #bytes #cb msg sk rand group_context confirmation_key interim_transcript_hash =
  let? msg_network = message_content_to_network msg in
  if not (Some? group_context = knows_group_context msg_network.sender) then
    internal_failure "message_compute_auth: bad optional group context"
  else (
    let? signature = compute_message_signature sk rand msg.wire_format msg_network group_context in
    let? confirmation_tag = (
      if msg.content_type = CT_commit then (
        let? confirmed_transcript_hash = compute_confirmed_transcript_hash msg signature interim_transcript_hash in
        let? confirmation_tag = compute_message_confirmation_tag confirmation_key confirmed_transcript_hash in
        return (Some confirmation_tag <: option bytes)
      ) else (
        return None
      )
    ) in
    return ({
      signature = signature;
      confirmation_tag = confirmation_tag;
    } <: message_auth bytes)
  )

(*** From/to plaintext ***)

val message_plaintext_to_message:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  public_message_nt bytes ->
  authenticated_content_nt bytes
let message_plaintext_to_message #bytes #bl pt =
  {
    wire_format = WF_mls_public_message;
    content = pt.content;
    auth = pt.auth;
  }

val message_to_message_plaintext:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  membership_key:bytes -> auth_msg:authenticated_content_nt bytes{auth_msg.wire_format == WF_mls_public_message} -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context auth_msg.content.sender} ->
  result (public_message_nt bytes)
let message_to_message_plaintext #bytes #cb membership_key auth_msg group_context =
  let? membership_tag = (
    match auth_msg.content.sender with
    | NT.S_member _ -> (
      let? res = compute_message_membership_tag membership_key auth_msg.content auth_msg.auth group_context in
      return (res <: membership_tag_nt bytes auth_msg.content.sender)
    )
    | _ -> return ()
  ) in
  return ({
    content = auth_msg.content;
    auth = auth_msg.auth;
    membership_tag;
  } <: public_message_nt bytes)

(*** From/to ciphertext ***)

val get_ciphertext_sample:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  bytes
let get_ciphertext_sample #bytes #cb ct =
  let len = kdf_length #bytes in
  if length ct <= len then
    ct
  else
    fst (unsafe_split ct len)

//Used in decryption
val message_ciphertext_to_sender_data_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  private_message_nt bytes ->
  sender_data_aad_nt bytes
let message_ciphertext_to_sender_data_aad #bytes #bl ct =
  ({
    group_id = ct.group_id;
    epoch = ct.epoch;
    content_type = ct.content_type;
  } <: sender_data_aad_nt bytes)

//Used in encryption
val message_to_sender_data_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  framed_content_nt bytes ->
  sender_data_aad_nt bytes
let message_to_sender_data_aad #bytes #bl content =
  ({
    group_id = content.group_id;
    epoch = content.epoch;
    content_type = content.content.content_type;
  } <: sender_data_aad_nt bytes)

val sender_data_key_nonce:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ciphertext_sample:bytes -> sender_data_secret:bytes ->
  result (lbytes bytes (aead_key_length #bytes) & lbytes bytes (aead_nonce_length #bytes))
let sender_data_key_nonce #bytes #cb ciphertext_sample sender_data_secret =
  let? sender_data_key = expand_with_label sender_data_secret (string_to_bytes #bytes "key") ciphertext_sample (aead_key_length #bytes) in
  let? sender_data_nonce = expand_with_label sender_data_secret (string_to_bytes #bytes "nonce") ciphertext_sample (aead_nonce_length #bytes) in
  return (sender_data_key, sender_data_nonce)

val decrypt_sender_data:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sender_data_aad_nt bytes -> ciphertext_sample:bytes -> sender_data_secret:bytes -> encrypted_sender_data:bytes ->
  result (sender_data_nt bytes)
let decrypt_sender_data #bytes #cb ad ciphertext_sample sender_data_secret encrypted_sender_data =
  let? (sender_data_key, sender_data_nonce) = sender_data_key_nonce ciphertext_sample sender_data_secret in
  let? sender_data = aead_decrypt sender_data_key sender_data_nonce (serialize (sender_data_aad_nt bytes) ad) encrypted_sender_data in
  from_option "decrypt_sender_data: malformed sender data" (parse (sender_data_nt bytes) sender_data)

val encrypt_sender_data:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sender_data_aad_nt bytes -> ciphertext_sample:bytes -> sender_data_secret:bytes -> sender_data_nt bytes ->
  result bytes
let encrypt_sender_data #bytes #cb ad ciphertext_sample sender_data_secret sender_data =
  let? (sender_data_key, sender_data_nonce) = sender_data_key_nonce ciphertext_sample sender_data_secret in
  aead_encrypt sender_data_key sender_data_nonce (serialize (sender_data_aad_nt bytes) ad) (serialize (sender_data_nt bytes) sender_data)

// Used in decryption
val message_ciphertext_to_ciphertext_content_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ct:private_message_nt bytes ->
  res:private_content_aad_nt bytes{res.content_type == ct.content_type}
let message_ciphertext_to_ciphertext_content_aad #bytes #bl ct =
  ({
    group_id = ct.group_id;
    epoch = ct.epoch;
    content_type = ct.content_type;
    authenticated_data = ct.authenticated_data;
  } <: private_content_aad_nt bytes)

val decrypt_ciphertext_content:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ad:private_content_aad_nt bytes -> aead_key bytes -> aead_nonce bytes -> ct:bytes ->
  result (private_content_tbe_nt bytes ad.content_type)
let decrypt_ciphertext_content #bytes #cb ad key nonce ct =
  let? ciphertext_content = aead_decrypt key nonce (serialize (private_content_aad_nt bytes) ad) ct in
  from_option "decrypt_ciphertext_content: malformed ciphertext content" (parse (private_content_tbe_nt bytes ad.content_type) ciphertext_content)

// Used in encryption
val message_to_ciphertext_content_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  content:framed_content_nt bytes ->
  res:private_content_aad_nt bytes{res.content_type == content.content.content_type}
let message_to_ciphertext_content_aad #bytes #bl content =
  ({
    group_id = content.group_id;
    epoch = content.epoch;
    content_type = content.content.content_type;
    authenticated_data = content.authenticated_data;
  } <: private_content_aad_nt bytes)

val encrypt_ciphertext_content:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ad:private_content_aad_nt bytes -> aead_key bytes -> aead_nonce bytes -> (private_content_tbe_nt bytes ad.content_type) ->
  result bytes
let encrypt_ciphertext_content #bytes #cb ad key nonce pt =
  aead_encrypt key nonce (serialize (private_content_aad_nt bytes) ad) (serialize (private_content_tbe_nt bytes ad.content_type) pt)

val apply_reuse_guard:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  lbytes bytes 4 -> aead_nonce bytes ->
  aead_nonce bytes
let apply_reuse_guard #bytes #cb reuse_guard nonce =
  let (nonce_head, nonce_tail) = unsafe_split #bytes nonce 4 in
  assume(length nonce_head == 4);
  assume(length nonce_tail == aead_nonce_length #bytes - 4);
  let new_nonce_head = xor nonce_head reuse_guard in
  concat #bytes new_nonce_head nonce_tail

val message_ciphertext_to_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:nat -> encryption_secret:bytes -> sender_data_secret:bytes -> private_message_nt bytes ->
  result (authenticated_content_nt bytes)
let message_ciphertext_to_message #bytes #cb l encryption_secret sender_data_secret ct =
  let? sender_data = (
    let sender_data_ad = message_ciphertext_to_sender_data_aad ct in
    decrypt_sender_data sender_data_ad (get_ciphertext_sample ct.ciphertext) sender_data_secret ct.encrypted_sender_data
  ) in
  let? rs_output = (
    let? sender_index = (
      if not (sender_data.leaf_index < pow2 l) then
        error "message_ciphertext_to_message: leaf_index too big"
      else
        return sender_data.leaf_index
    ) in
    let? leaf_tree_secret = leaf_kdf encryption_secret (sender_index <: MLS.Tree.leaf_index l 0) in
    let? init_ratchet = (
      match ct.content_type with
      | CT_application -> init_application_ratchet leaf_tree_secret
      | _ -> init_handshake_ratchet leaf_tree_secret
    ) in
    ratchet_get_generation_key init_ratchet sender_data.generation
  ) in
  let? ciphertext_content = (
    let nonce = rs_output.nonce in
    let key = rs_output.key in
    let patched_nonce = apply_reuse_guard sender_data.reuse_guard nonce in
    let ciphertext_content_ad = message_ciphertext_to_ciphertext_content_aad ct in
    decrypt_ciphertext_content ciphertext_content_ad key patched_nonce ct.ciphertext
  ) in
  return ({
    wire_format = WF_mls_private_message;
    content = {
      group_id = ct.group_id;
      epoch = ct.epoch;
      sender = NT.S_member sender_data.leaf_index;
      authenticated_data = ct.authenticated_data;
      content = {
        content_type = ct.content_type;
        content = ciphertext_content.data.content;
      };
    };
    auth = {
      signature = ciphertext_content.data.auth.signature;
      confirmation_tag = ciphertext_content.data.auth.confirmation_tag;
    };
  } <: authenticated_content_nt bytes)

val get_serializeable_bytes:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  bytes ->
  result (mls_bytes bytes)
let get_serializeable_bytes #bytes #bl b =
  if not (length b < pow2 30) then (
    internal_failure "get_serializeable_bytes: buffer too long"
  ) else (
    return b
  )

val message_to_message_ciphertext:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ratchet_state bytes -> lbytes bytes 4 -> bytes -> msg:authenticated_content_nt bytes{msg.wire_format == WF_mls_private_message} ->
  result (private_message_nt bytes & ratchet_state bytes)
let message_to_message_ciphertext #bytes #cb ratchet reuse_guard sender_data_secret auth_msg =
  let? ciphertext = (
    let? key_nonce = ratchet_get_key ratchet in
    let key = key_nonce.key in
    let patched_nonce = apply_reuse_guard reuse_guard key_nonce.nonce in
    let ciphertext_content: private_content_tbe_nt bytes (auth_msg.content.content.content_type) = {
      data = {
        content = auth_msg.content.content.content;
        auth = auth_msg.auth;
      };
      padding = [];
    } in
    let ciphertext_content_ad = message_to_ciphertext_content_aad auth_msg.content in
    let? ciphertext = encrypt_ciphertext_content ciphertext_content_ad key patched_nonce ciphertext_content in
    get_serializeable_bytes ciphertext
  ) in
  let? encrypted_sender_data = (
    if not (NT.S_member? auth_msg.content.sender) then
      error "message_to_message_ciphertext: sender is not a member"
    else if not (ratchet.generation < pow2 32) then
      internal_failure "message_to_message_ciphertext: ratchet too big"
    else (
      let sender_data_ad = message_to_sender_data_aad auth_msg.content in
      let sender_data = ({
        leaf_index = NT.S_member?.leaf_index auth_msg.content.sender;
        generation = ratchet.generation;
        reuse_guard = reuse_guard;
      }) in
      let? encrypted_sender_data = encrypt_sender_data sender_data_ad (get_ciphertext_sample ciphertext) sender_data_secret sender_data in
      get_serializeable_bytes encrypted_sender_data
    )
  ) in
  let? new_ratchet = ratchet_next_state ratchet in
  return (({
    group_id = auth_msg.content.group_id;
    epoch = auth_msg.content.epoch;
    content_type = auth_msg.content.content.content_type;
    authenticated_data = auth_msg.content.authenticated_data;
    encrypted_sender_data = encrypted_sender_data;
    ciphertext = ciphertext;
  } <: private_message_nt bytes), new_ratchet)
