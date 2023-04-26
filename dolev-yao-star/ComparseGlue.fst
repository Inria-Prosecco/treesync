module ComparseGlue

open SecrecyLabels
open LabeledCryptoAPI
open CryptoLib
open Comparse

(*** Parser for principals ***)

val ps_char: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes Char.char
let ps_char #bytes #bl =
  let char_pred (n:nat_lbytes 4) = n < 0xd7ff || (n >= 0xe000 && n <= 0x10ffff) in
  mk_isomorphism Char.char (refine (ps_nat_lbytes 4) char_pred) (fun c -> Char.char_of_int c) (fun c -> Char.int_of_char c)

val ps_char_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes -> c:Char.char ->
  Lemma (is_well_formed_prefix ps_char pre c)
  [SMTPat (is_well_formed_prefix ps_char pre c)]
let ps_char_is_well_formed #bytes #bl pre c = ()

val ps_string: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes string
let ps_string #bytes #bl =
  isomorphism (ps_seq ps_char) ({
    a_to_b = (fun s -> String.string_of_list (Seq.seq_to_list s));
    b_to_a = (fun s -> Seq.seq_of_list (String.list_of_string s));
    a_to_b_to_a = (fun s -> String.list_of_string_of_list (Seq.seq_to_list s); Seq.lemma_seq_list_bij s);
    b_to_a_to_b = (fun s -> String.string_of_list_of_string s; Seq.lemma_list_seq_bij (String.list_of_string s));
  })

val ps_string_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes -> s:string ->
  Lemma (is_well_formed_prefix ps_string pre s)
  [SMTPat (is_well_formed_prefix ps_string pre s)]
let ps_string_is_well_formed #bytes #bl pre s =
  Seq.lemma_list_seq_bij (String.list_of_string s);
  for_allP_eq (is_well_formed_prefix ps_char pre) (String.list_of_string s)

[@@is_parser; is_parser_for (`%SecrecyLabels.principal)]
val ps_principal: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes SecrecyLabels.principal
let ps_principal #bytes #bl =
  mk_trivial_isomorphism ps_string

(*** Parser for nats ***)

[@@is_parser; is_parser_for (`%nat)]
val ps_nat: #bytes:Type0 -> {| bytes_like bytes |} -> parser_serializer bytes nat
let ps_nat #bytes #bl = ps_nat

(*** Instances for DY* bytes ***)

instance dy_bytes_like: bytes_like bytes = {
  length = CryptoLib.len;

  empty = CryptoLib.empty;
  empty_length = (fun () -> len_empty ());
  recognize_empty = (fun b -> b = CryptoLib.empty);

  concat = (fun (b1:bytes) (b2:bytes) -> CryptoLib.raw_concat b1 b2);
  concat_length = (fun b1 b2 -> len_raw_concat b1 b2);

  split = (fun b i ->
    match CryptoLib.split_at i b with
    | Success (b1, b2) -> Some (b1, b2)
    | Error _ -> None
  );

  split_length = (fun b i -> len_split_at i b);
  split_concat = (fun b1 b2 ->
    split_at_raw_concat_lemma b1 b2
  );
  concat_split = (fun b i ->
    raw_concat_split_at_lemma i b
  );

  to_nat = (fun b ->
    match bytes_to_nat_lbytes b with
    | Success x -> Some x
    | Error _ -> None
  );
  from_nat = (fun sz n ->
    nat_lbytes_to_bytes sz n
  );

  from_to_nat = (fun sz n -> nat_lbytes_to_bytes_to_nat_lbytes sz n);
  to_from_nat = (fun b -> bytes_to_nat_lbytes_to_bytes b);
}

let bytes_pre_is_compatible_intro
  (#bytes:Type0) {|bytes_like bytes|} (pre:bytes -> prop)
  (empty_proof:squash(pre empty))
  (concat_proof:(b1:bytes{pre b1} -> b2:bytes{pre b2} -> Lemma (pre (concat b1 b2))))
  (split_proof:(b:bytes{pre b} -> i:nat{Some? (split #bytes b i)} -> Lemma (pre (fst (Some?.v (split b i))) /\ pre (snd (Some?.v (split b i))))))
  (from_nat_proof:(sz:nat -> n:nat_lbytes sz -> Lemma (pre (from_nat sz n))))
  : squash (bytes_pre_is_compatible pre)
  =
  FStar.Classical.forall_intro_2 concat_proof;
  FStar.Classical.forall_intro_2 split_proof;
  FStar.Classical.forall_intro_2 from_nat_proof

val bytes_compatible_pre_is_well_formed: p:global_usage -> i:timestamp -> Lemma (bytes_pre_is_compatible (LabeledCryptoAPI.is_valid p i))
  [SMTPat (bytes_pre_is_compatible (LabeledCryptoAPI.is_valid p i))]
let bytes_compatible_pre_is_well_formed p i =
  bytes_pre_is_compatible_intro #bytes (LabeledCryptoAPI.is_valid p i)
    (LabeledCryptoAPI.empty_lemma #p #i)
    (fun b1 b2 -> LabeledCryptoAPI.raw_concat_lemma #p #i #private_label b1 b2)
    (fun b l -> LabeledCryptoAPI.split_at_lemma #p #i #private_label l b)
    (fun sz n -> LabeledCryptoAPI.nat_lbytes_to_bytes_lemma #p #i sz n)

// Correct argument order to enable curryfication
let is_msg p l i b = LabeledCryptoAPI.is_msg p i b l

val bytes_compatible_pre_is_msg: p:global_usage -> l:label -> i:timestamp -> Lemma (bytes_pre_is_compatible (is_msg p l i))
  [SMTPat (bytes_pre_is_compatible (is_msg p l i))]
let bytes_compatible_pre_is_msg p l i =
  bytes_pre_is_compatible_intro #bytes (is_msg p l i)
    (LabeledCryptoAPI.empty_lemma #p #i)
    (fun b1 b2 -> LabeledCryptoAPI.raw_concat_lemma #p #i #l b1 b2)
    (fun b sz -> LabeledCryptoAPI.split_at_lemma #p #i #l sz b)
    (fun sz n -> LabeledCryptoAPI.nat_lbytes_to_bytes_lemma #p #i sz n)


instance msg_bytes_like (p:global_usage) (l:label) (i:timestamp): Comparse.Bytes.bytes_like (msg p i l) =
  Comparse.Bytes.refine_bytes_like bytes (is_msg p l i)
