module Comparse.Bytes.SMTPats

open Comparse.Bytes.Typeclass

// Expose some lemmas of the `bytes_like` typeclass via SMT patterns

val empty_length_lemma: bytes:Type0 -> {|bl:bytes_like bytes|} -> Lemma
  (length (empty #bytes #bl) == 0)
  [SMTPat (length (empty #bytes #bl))]
let empty_length_lemma bytes #bl = empty_length #bytes ()

val concat_length_lemma: #bytes:Type0 -> {|bl:bytes_like bytes|} -> b1:bytes -> b2:bytes -> Lemma
  (length (concat b1 b2) == (length b1) + (length b2))
  [SMTPat (length #bytes #bl (concat b1 b2))]
let concat_length_lemma #bytes #bl b1 b2 = concat_length b1 b2

val split_length_lemma: #bytes:Type0 -> {|bl:bytes_like bytes|} -> b:bytes -> i:nat{i <= length b} -> Lemma
  (match split b i with
    | Some (b1, b2) -> length b1 == i /\ i+length b2 == length b
    | None -> True
  )
  [SMTPat (split #bytes #bl b i)]
let split_length_lemma #bytes #bl b i = split_length b i
