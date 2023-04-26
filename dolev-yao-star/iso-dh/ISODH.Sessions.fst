/// ISODH.Sessions (implementation)
/// ================================
module ISODH.Sessions

module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

%splice [ps_session_st_generic] (gen_parser (`session_st_generic))
%splice [ps_session_st_generic_is_well_formed] (gen_is_well_formed_lemma (`session_st_generic))

instance session_st_parseable_serializeable: parseable_serializeable bytes session_st
 = mk_parseable_serializeable ps_session_st_generic

let parse_session_st (serialized_session:bytes) : result session_st =
  match parse session_st serialized_session with
  | Some s -> Success s
  | None -> Error "could not parse session"

let serialize_valid_session_st i p si vi st =
  serialize_wf_lemma session_st (ComparseGlue.is_msg isodh_global_usage (readers [V p si vi]) i) st;
  (serialize session_st st <: bytes)

let parse_valid_serialize_session_st_lemma i p si vi ss =
  parse_serialize_inv_lemma #bytes session_st ss
