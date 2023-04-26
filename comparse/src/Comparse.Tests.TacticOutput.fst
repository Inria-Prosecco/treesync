module Comparse.Tests.TacticOutput

open FStar.IO
open FStar.All
open FStar.Mul
open Comparse

irreducible let test = ()

(*** Utility functions, from MLS* ***)

let bytes = (Seq.seq UInt8.t)
instance bytes_like_bytes: bytes_like bytes = seq_u8_bytes_like

val hex_string_to_hex_digit: s:string{String.strlen s == 1} -> ML (n:nat{n<16})
let hex_string_to_hex_digit s =
  if s = "0" then 0
  else if s = "1" then 1
  else if s = "2" then 2
  else if s = "3" then 3
  else if s = "4" then 4
  else if s = "5" then 5
  else if s = "6" then 6
  else if s = "7" then 7
  else if s = "8" then 8
  else if s = "9" then 9
  else if s = "A" then 10
  else if s = "B" then 11
  else if s = "C" then 12
  else if s = "D" then 13
  else if s = "E" then 14
  else if s = "F" then 15
  else if s = "a" then 10
  else if s = "b" then 11
  else if s = "c" then 12
  else if s = "d" then 13
  else if s = "e" then 14
  else if s = "f" then 15
  else failwith "string_to_hex_digit: digit is not in [0-9A-Fa-f]"

val hex_string_to_byte: s:string{String.strlen s == 2} -> ML (n:nat{n<256})
let hex_string_to_byte s =
  let open FStar.Mul in
  let d1 = hex_string_to_hex_digit (String.sub s 0 1) in
  let d2 = hex_string_to_hex_digit (String.sub s 1 1) in
  16*d1 + d2

//We do recursion on lists, because recursing on a string is slow
val hex_list_char_to_list_u8: list Char.char -> ML (list UInt8.t)
let rec hex_list_char_to_list_u8 l =
  match l with
  | [] -> []
  | [h] -> failwith "string_to_bytes: size is not a multiple of two"
  | h1::h2::t ->
    String.list_of_string_of_list [h1; h2];
    let cur_digit = hex_string_to_byte (String.string_of_list [h1; h2]) in
    let b0 = UInt8.uint_to_t cur_digit in
    let bs = hex_list_char_to_list_u8 t in
    b0::bs

val hex_string_to_bytes: string -> ML bytes
let hex_string_to_bytes s =
  //For some reason, introducing this let helps F*'s type system
  let res = hex_list_char_to_list_u8 (String.list_of_string s) in
  Seq.seq_of_list res

val hex_digit_to_hex_string: n:nat{n<16} -> string
let hex_digit_to_hex_string n =
  match n with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"
  | 10 -> "A"
  | 11 -> "B"
  | 12 -> "C"
  | 13 -> "D"
  | 14 -> "E"
  | 15 -> "F"

val nat_to_hex_string_aux: n:nat -> string
let rec nat_to_hex_string_aux n =
  if n = 0 then ""
  else (nat_to_hex_string_aux (n/16))^(hex_digit_to_hex_string (n%16))

val nat_to_hex_string: n:nat -> string
let nat_to_hex_string n =
  if n = 0 then "00"
  else (
    let res = nat_to_hex_string_aux n in
    if (String.length res) % 2 = 1 then
      "0" ^ res
    else
      res
  )

(*
val byte_to_hex_string: n:nat{n<256} -> string
let byte_to_hex_string n =
  (hex_digit_to_hex_string (n/16)) ^ (hex_digit_to_hex_string (n%16))

val bytes_to_hex_string: bytes -> string
let bytes_to_hex_string b =
  FStar.String.concat "" (List.Tot.map (fun x -> byte_to_hex_string (UInt8.v x)) (FStar.Seq.seq_to_list b))
  *)

(*** Unit tests ***)

val parse_ok: #a:eqtype -> parser_serializer bytes a -> string -> a -> ML bool
let parse_ok #a ps_a s x =
  (ps_prefix_to_ps_whole ps_a).parse (hex_string_to_bytes s) = Some x

val parse_fail: #a:Type -> parser_serializer bytes a -> string -> ML bool
let parse_fail #a ps_a s =
  None? ((ps_prefix_to_ps_whole ps_a).parse (hex_string_to_bytes s))

let from_string = hex_string_to_bytes
val with_length: n:nat -> bytes -> ML (b:bytes{Seq.length b == n})
let with_length n b =
  if Seq.length b = n then
    b
  else
    failwith "with_length: wrong length"

[@@ test]
let ps_nat_lbytes_is_big_endian (): ML bool =
  parse_ok
    (ps_nat_lbytes 8)
    "0123456789ABCDEF"
    0x0123456789ABCDEF

[@@ test]
let ps_tls_nat_1_low (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 8)-1}))
    "00"
    0

[@@ test]
let ps_tls_nat_1_high (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 8)-1}))
    "FF"
    ((pow2 8)-1)

[@@ test]
let ps_tls_nat_2_low_boundary (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 8)}))
    "0000"
    0

[@@ test]
let ps_tls_nat_2_low (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 16)-1}))
    "0000"
    0

[@@ test]
let ps_tls_nat_2_high (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 16)-1}))
    "FFFF"
    ((pow2 16)-1)

[@@ test]
let ps_tls_nat_3_low_boundary (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 16)}))
    "000000"
    0

[@@ test]
let ps_tls_nat_3_low (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 24)-1}))
    "000000"
    0

[@@ test]
let ps_tls_nat_3_high (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 24)-1}))
    "FFFFFF"
    ((pow2 24)-1)

[@@ test]
let ps_tls_nat_4_low_boundary (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 24)}))
    "00000000"
    0


[@@ test]
let ps_tls_nat_4_low (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 32)-1}))
    "00000000"
    0

[@@ test]
let ps_tls_nat_4_high (): ML bool =
  parse_ok
    (ps_tls_nat ({min=0; max=(pow2 32)-1}))
    "FFFFFFFF"
    ((pow2 32)-1)

val mk_quic_nat: sz:nat{sz < 4} -> n:nat{n < normalize_term (pow2 (8*(pow2 sz)-2))} -> string
let mk_quic_nat sz n =
  nat_to_hex_string (sz * (pow2 (8*(pow2 sz)-2)) + n)

[@@ test]
let ps_quic_nat_1_low_ok (): ML bool =
  let n = normalize_term #nat (0) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 0 n)
    n

[@@ test]
let ps_quic_nat_1_high_ok (): ML bool =
  let n = normalize_term #nat ((pow2 (1*8-2))-1) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 0 n)
    n

[@@ test]
let ps_quic_nat_2_fail (): ML bool =
  let n = normalize_term #nat ((pow2 (1*8-2))-1) in
  parse_fail
    ps_quic_nat
    (mk_quic_nat 1 n)

[@@ test]
let ps_quic_nat_2_low_ok (): ML bool =
  let n = normalize_term #nat (pow2 (1*8-2)) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 1 n)
    n

[@@ test]
let ps_quic_nat_2_high_ok (): ML bool =
  let n = normalize_term #nat ((pow2 (2*8-2))-1) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 1 n)
    n

[@@ test]
let ps_quic_nat_4_fail (): ML bool =
  let n = normalize_term #nat ((pow2 (2*8-2))-1) in
  parse_fail
    ps_quic_nat
    (mk_quic_nat 2 n)

[@@ test]
let ps_quic_nat_4_low_ok (): ML bool =
  let n = normalize_term #nat (pow2 (2*8-2)) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 2 n)
    n

[@@ test]
let ps_quic_nat_4_high_ok (): ML bool =
  let n = normalize_term #nat ((pow2 (4*8-2))-1) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 2 n)
    n

[@@ test]
let ps_quic_nat_8_fail (): ML bool =
  let n = normalize_term #nat ((pow2 (4*8-2))-1) in
  parse_fail
    ps_quic_nat
    (mk_quic_nat 3 n)

[@@ test]
let ps_quic_nat_8_low_ok (): ML bool =
  let n = normalize_term #nat (pow2 (4*8-2)) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 3 n)
    n

[@@ test]
let ps_quic_nat_8_high_ok (): ML bool =
  let n = normalize_term #nat ((pow2 (8*8-2))-1) in
  parse_ok
    ps_quic_nat
    (mk_quic_nat 3 n)
    n

type simple_record = {
  simple_record_1: nat_lbytes 1;
  simple_record_2: nat_lbytes 2;
  simple_record_3: nat_lbytes 3;
  simple_record_4: nat_lbytes 4;
}

%splice [ps_simple_record] (gen_parser (`simple_record))

[@@ test]
let ps_simple_record_ok (): ML bool =
  parse_ok
    ps_simple_record
    "11222233333344444444"
    ({
      simple_record_1 = 0x11;
      simple_record_2 = 0x2222;
      simple_record_3 = 0x333333;
      simple_record_4 = 0x44444444;
    })

type sum_type_with_num_tag (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_num_tag 2 0X002A] SumTypeWithNumTag_1: sum_type_with_num_tag bytes
  | [@@@ with_num_tag 2 0X0539] SumTypeWithNumTag_2: tls_bytes bytes ({min=0; max=255}) -> sum_type_with_num_tag bytes
  | [@@@ with_num_tag 2 0X0FFF] SumTypeWithNumTag_3: tls_seq bytes (ps_nat_lbytes 2) ({min=0; max=255}) -> sum_type_with_num_tag bytes
  | [@@@ with_num_tag 2 0XAAAA] SumTypeWithNumTag_4: nat_lbytes 8 -> sum_type_with_num_tag bytes

%splice [ps_sum_type_with_num_tag] (gen_parser (`sum_type_with_num_tag))

[@@ test]
let ps_sum_type_with_num_tag_1 (): ML bool =
  parse_ok
    ps_sum_type_with_num_tag
    "002A"
    SumTypeWithNumTag_1

[@@ test]
let ps_sum_type_with_num_tag_2 (): ML bool =
  parse_ok
    ps_sum_type_with_num_tag
    "053903C0FFEE"
    (SumTypeWithNumTag_2 (with_length 3 (from_string "C0FFEE")))

[@@ test]
let ps_sum_type_with_num_tag_3 (): ML bool =
  let l: Seq.seq (nat_lbytes 2) = Seq.seq_of_list [0x1111; 0x4444; 0xAAAA; 0xFFFF] in
  if bytes_length #bytes (ps_nat_lbytes 2) (Seq.seq_to_list l) = 8 then
    parse_ok
      ps_sum_type_with_num_tag
      "0FFF0811114444AAAAFFFF"
      (SumTypeWithNumTag_3 l)
  else
    failwith "internal error: wrong length"

[@@ test]
let ps_sum_type_with_num_tag_4 (): ML bool =
  parse_ok
    ps_sum_type_with_num_tag
    "AAAA0123456789ABCDEF"
    (SumTypeWithNumTag_4 0x0123456789ABCDEF)

type enum_singleton =
  | [@@@ with_num_tag 4 0x12345678] EnumSingleton: enum_singleton

%splice [ps_enum_singleton] (gen_parser (`enum_singleton))

[@@ test]
let ps_enum_singleton_ok (): ML bool =
  parse_ok
    ps_enum_singleton
    "12345678"
    EnumSingleton

type enum_multi =
  | [@@@ with_num_tag 4 0x12345678] EnumMulti_1: enum_multi
  | [@@@ with_num_tag 4 0x87654321] EnumMulti_2: enum_multi
  | [@@@ with_num_tag 4 0x10203040] EnumMulti_3: enum_multi
  | [@@@ with_num_tag 4 0x50607080] EnumMulti_4: enum_multi

%splice [ps_enum_multi] (gen_parser (`enum_multi))

[@@ test]
let ps_enum_multi_1 (): ML bool =
  parse_ok
    ps_enum_multi
    "12345678"
    EnumMulti_1

[@@ test]
let ps_enum_multi_2 (): ML bool =
  parse_ok
    ps_enum_multi
    "87654321"
    EnumMulti_2

[@@ test]
let ps_enum_multi_3 (): ML bool =
  parse_ok
    ps_enum_multi
    "10203040"
    EnumMulti_3

[@@ test]
let ps_enum_multi_4 (): ML bool =
  parse_ok
    ps_enum_multi
    "50607080"
    EnumMulti_4

type sum_type_with_enum_tag (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag EnumMulti_1] SumTypeWithEnumTag_1: sum_type_with_enum_tag bytes
  | [@@@ with_tag EnumMulti_2] SumTypeWithEnumTag_2: tls_bytes bytes ({min=0; max=255}) -> sum_type_with_enum_tag bytes
  | [@@@ with_tag EnumMulti_3] SumTypeWithEnumTag_3: tls_seq bytes (ps_nat_lbytes 2) ({min=0; max=255}) -> sum_type_with_enum_tag bytes
  | [@@@ with_tag EnumMulti_4] SumTypeWithEnumTag_4: nat_lbytes 8 -> sum_type_with_enum_tag bytes

%splice [ps_sum_type_with_enum_tag] (gen_parser (`sum_type_with_enum_tag))

[@@ test]
let ps_sum_type_with_enum_tag_1 (): ML bool =
  parse_ok
    ps_sum_type_with_enum_tag
    "12345678"
    SumTypeWithEnumTag_1

[@@ test]
let ps_sum_type_with_enum_tag_2 (): ML bool =
  parse_ok
    ps_sum_type_with_enum_tag
    "8765432103C0FFEE"
    (SumTypeWithEnumTag_2 (with_length 3 (from_string "C0FFEE")))

[@@ test]
let ps_sum_type_with_enum_tag_3 (): ML bool =
  let l: Seq.seq (nat_lbytes 2) = Seq.seq_of_list [0x1111; 0x4444; 0xAAAA; 0xFFFF] in
  if bytes_length #bytes (ps_nat_lbytes 2) (Seq.seq_to_list l) = 8 then
    parse_ok
      ps_sum_type_with_enum_tag
      "102030400811114444AAAAFFFF"
      (SumTypeWithEnumTag_3 l)
  else
    failwith "internal error: wrong length"

[@@ test]
let ps_sum_type_with_enum_tag_4 (): ML bool =
  parse_ok
    ps_sum_type_with_enum_tag
    "506070800123456789ABCDEF"
    (SumTypeWithEnumTag_4 0x0123456789ABCDEF)

(*** Metaprogram to launch tests ***)

open FStar.Tactics

inline_for_extraction noextract
val list_to_list: list (string & fv) -> Tac term
let rec list_to_list l =
  match l with
  | [] -> `([])
  | (s,f)::t -> `((((`#(pack (Tv_Const (C_String s))))), (`#(pack (Tv_FVar f))))::(`#(list_to_list t)))


inline_for_extraction noextract
val list_tests: unit -> Tac term
let list_tests () =
  let tests_fv = List.Tot.rev (lookup_attr (`test) (top_env ())) in
  list_to_list (Tactics.Util.map (fun test_fv ->
    guard (Cons? (inspect_fv test_fv));
    (List.Tot.last (inspect_fv test_fv), test_fv)
  ) tests_fv)

val all_tests: list (string & (unit -> ML bool))
let all_tests = synth_by_tactic (fun () -> exact (list_tests ()))

val execute_one_test: string -> (unit -> ML bool) -> ML unit
let execute_one_test s t =
  IO.print_string ("Testing " ^ s ^ "...");
  if t () then (
    IO.print_string " ok.\n"
  ) else (
    IO.print_string " failed.\n";
    exit 1
  )

val execute_tests: list (string & (unit -> ML bool)) -> ML unit
let rec execute_tests l =
  match l with
  | [] -> ()
  | (s,f)::t -> (
    execute_one_test s f;
    execute_tests t
  )

let main = execute_tests all_tests
