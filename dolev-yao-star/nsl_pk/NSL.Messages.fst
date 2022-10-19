/// NSL.Messages (implementation)
/// ==============================
module NSL.Messages

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
module A = LabeledCryptoAPI
//module C = CryptoLib

open Comparse
open ComparseGlue

let initiate (a:principal) (b:principal) (n_a:bytes) : event =
  ("Initiate",[(string_to_bytes a);(string_to_bytes b);n_a])
let respond (a:principal) (b:principal) (n_a:bytes) (n_b:bytes) : event =
  ("Respond",[(string_to_bytes a);(string_to_bytes b);n_a;n_b])
let finishI (a:principal) (b:principal) (n_a:bytes) (n_b:bytes) : event =
  ("FinishI",[(string_to_bytes a);(string_to_bytes b);n_a;n_b])
let finishR (a:principal) (b:principal) (n_a:bytes) (n_b:bytes) : event =
  ("FinishR",[(string_to_bytes a);(string_to_bytes b);n_a;n_b])

noeq type message_generic (bytes:Type0) {|bytes_like bytes|} =
  | Msg1: n_a: bytes -> a:principal -> message_generic bytes
  | Msg2: n_a: bytes -> n_b:bytes -> b:principal -> message_generic bytes
  | Msg3: n_b: bytes -> a:principal -> message_generic bytes

%splice [ps_message_generic] (gen_parser (`message_generic))
%splice [ps_message_generic_is_well_formed] (gen_is_well_formed_lemma (`message_generic))

type message = message_generic bytes

instance message_parseable_serializeable: parseable_serializeable bytes message
 = mk_parseable_serializeable ps_message_generic

let parse_message (m:bytes) =
  match parse message m with
  | Some res -> Success res
  | None -> Error "Bad message format"

let nsl_key_usages : A.key_usages = A.default_key_usages

let ppred (i:nat) s pk m: prop =
    (exists p. A.get_sk_label nsl_key_usages pk == readers [P p] /\
    (match parse_message m with
    | Success (Msg2 n_a n_b b) ->
       (did_event_occur_before i b (respond p b n_a n_b)) /\
       (was_rand_generated_before i n_b (readers [P p; P b]) (nonce_usage "NSL.nonce"))
    | Success (Msg1 n_a a) ->
       (did_event_occur_before i a (initiate a p n_a)) /\
       (was_rand_generated_before i n_a (readers [P a; P p]) (nonce_usage "NSL.nonce"))
    | Success (Msg3 n_b a) ->
       (exists n_a. did_event_occur_before i a (finishI a p n_a n_b))
    | _ -> False))
let apred i s k m ad: prop = True
let spred i s k m: prop = True
let mpred i s k m: prop = True

let nsl_usage_preds : A.usage_preds = {
  A.can_pke_encrypt = ppred;
  A.can_aead_encrypt =  apred;
  A.can_sign = spred;
  A.can_mac = mpred
}

let nsl_global_usage : A.global_usage = {
  A.key_usages = nsl_key_usages;
  A.usage_preds = nsl_usage_preds;
}

let msg i l = A.msg nsl_global_usage i l

let my_is_msg_pre (l:label) (i:timestamp): bytes_compatible_pre bytes = ComparseGlue.is_msg nsl_global_usage l i

val valid_message: i:nat -> m:message -> l:label -> Type0
let valid_message i m l =
  is_well_formed message (my_is_msg_pre l i) m

val serialize_valid_message: i:nat -> m:message -> l:label{valid_message i m l} -> msg i l
let serialize_valid_message i m l =
  serialize_wf_lemma message (my_is_msg_pre l i) m;
  (serialize message m <: bytes)

let parse_serialize_valid_message_lemma (i:nat) (m:message) (l:label) : Lemma
    (valid_message i m l ==>
     (Success m == parse_message (serialize_valid_message i m l)))
    [SMTPat (parse_message (serialize_valid_message i m l))] =
    parse_serialize_inv_lemma #bytes message m

val parse_valid_message: #i:nat -> #l:label -> w:msg i l ->
                        r:result message{match r with
                                 | Success m -> Success m == parse_message w /\
					       valid_message i m l
                                 | Error s -> True}
let parse_valid_message #i #l w =
  parse_wf_lemma message (my_is_msg_pre l i) w;
  parse_message w
