/// ISODH.Messages (implementation)
/// ================================
module ISODH.Messages

module A = LabeledCryptoAPI

%splice [ps_sigval_generic] (gen_parser (`sigval_generic))
%splice [ps_sigval_generic_is_well_formed] (gen_is_well_formed_lemma (`sigval_generic))

instance sigval_parseable_serializeable: parseable_serializeable bytes sigval
 = mk_parseable_serializeable ps_sigval_generic

let parse_sigval t : result sigval =
  match (parse sigval t) with
  | Some x -> Success x
  | None -> Error "can't parse sigval"

let sigval_msg2 (#i:nat) (b:principal) (gx:msg i public) (gy:msg i public) = //: msg i public =
  parse_serialize_inv_lemma #bytes sigval (SigMsg2 b gx gy);
  serialize_wf_lemma sigval (ComparseGlue.is_msg isodh_global_usage public i) (SigMsg2 b gx gy);
  (serialize sigval (SigMsg2 b gx gy) <: bytes)

let sigval_msg3 (#i:nat) (a:principal) (gx:msg i public) (gy:msg i public) = //: msg i public =
  parse_serialize_inv_lemma #bytes sigval (SigMsg3 a gx gy);
  serialize_wf_lemma sigval (ComparseGlue.is_msg isodh_global_usage public i) (SigMsg3 a gx gy);
  (serialize sigval (SigMsg3 a gx gy) <: bytes)

%splice [ps_iso_msg_generic] (gen_parser (`iso_msg_generic))
//%splice [ps_iso_msg_generic_is_well_formed] (gen_is_well_formed_lemma (`iso_msg_generic))

instance iso_msg_parseable_serializeable (i:nat) : parseable_serializeable (msg i public) (iso_msg i)
 = mk_parseable_serializeable (ps_iso_msg_generic i)

let serialize_msg (i:nat) (m:iso_msg i) : msg i public =
  serialize _ m

let parse_msg (#i:nat) (w:msg i public) : result (iso_msg i) =
  match parse _ w with
  | Some res -> Success res
  | None -> Error "parse_msg: bad format"

//This sanity check can be removed?
let parse_serialize_msg_lemma #i m : Lemma (parse_msg #i (serialize_msg i m) == Success m) =
  parse_serialize_inv_lemma #(msg i public) _ m
