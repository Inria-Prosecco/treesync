module Comparse.Parser

open FStar.List.Tot
open Comparse.Bytes.Typeclass
open Comparse.Utils

#set-options "--fuel 0 --ifuel 2"

#push-options "--fuel 1"
let rec for_allP_eq #a pre l =
  match l with
  | [] -> ()
  | h::t -> for_allP_eq pre t
#pop-options

let rec add_prefixes #bytes #bl l suffix =
  match l with
  | [] -> suffix
  | h::t -> concat h ((add_prefixes t suffix))

let rec prefixes_length #bytes #bl l =
  match l with
  | [] -> 0
  | h::t -> length h + prefixes_length t

let is_well_formed_partial_weaken #bytes #bl #a ps_a pre_strong pre_weak x =
  for_allP_eq pre_strong (ps_a.serialize x);
  for_allP_eq pre_weak (ps_a.serialize x)

let is_not_unit #bytes #bl #a ps_a = forall b. length b == 0 ==> ps_a.parse b == None

(*** Helper functions ***)

#push-options "--ifuel 1 --fuel 1"
val for_allP_append: #a:Type -> pre:(a -> prop) -> l1:list a -> l2:list a -> Lemma
  (for_allP pre (l1@l2) <==> for_allP pre l1 /\ for_allP pre l2)
  [SMTPat (for_allP pre (l1@l2))]
let rec for_allP_append #a pre l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> for_allP_append pre t l2
#pop-options

#push-options "--ifuel 1 --fuel 1"
val add_prefixes_add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> l1:list bytes -> l2:list bytes -> suffix:bytes -> Lemma
  (add_prefixes l1 (add_prefixes l2 suffix) == add_prefixes (l1@l2) suffix)
let rec add_prefixes_add_prefixes l1 l2 suffix =
  match l1 with
  | [] -> ()
  | h::t -> add_prefixes_add_prefixes t l2 suffix
#pop-options

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_length: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (length (add_prefixes l suffix) == prefixes_length l + length suffix)
let rec add_prefixes_length #bytes #bl l suffix =
  match l with
  | [] -> ()
  | h::t ->
    add_prefixes_length t suffix;
    concat_length h (add_prefixes t suffix)
#pop-options

val prefixes_is_empty: #bytes:Type0 -> {|bytes_like bytes|} -> list bytes -> bool
let prefixes_is_empty l = List.Tot.for_all (fun b -> length b = 0) l

#push-options "--fuel 1 --ifuel 1"
val for_allP_pre_to_pre_add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> l:list bytes -> suffix:bytes -> Lemma
  (requires for_allP pre l /\ pre suffix)
  (ensures pre (add_prefixes l suffix))
let rec for_allP_pre_to_pre_add_prefixes #bytes #bl pre l suffix =
  match l with
  | [] -> ()
  | h::t -> for_allP_pre_to_pre_add_prefixes pre t suffix
#pop-options

#push-options "--fuel 1 --ifuel 1"
val pre_add_prefixes_to_for_allP_pre: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> l:list bytes -> suffix:bytes -> Lemma
  (requires pre (add_prefixes l suffix))
  (ensures for_allP pre l /\ pre suffix)
let rec pre_add_prefixes_to_for_allP_pre #bytes #bl pre l suffix =
  match l with
  | [] -> ()
  | h::t -> (
    concat_length h (add_prefixes t suffix);
    split_concat h (add_prefixes t suffix);
    assert(split (add_prefixes l suffix) (length h) == Some (h, add_prefixes t suffix));
    pre_add_prefixes_to_for_allP_pre pre t suffix
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val prefixes_length_concat: #bytes:Type0 -> {|bytes_like bytes|} -> l1:list bytes -> l2:list bytes -> Lemma
  (prefixes_length (l1@l2) == (prefixes_length l1) + (prefixes_length l2))
let rec prefixes_length_concat #bytes #bl l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> prefixes_length_concat t l2
#pop-options

(*** Parser combinators ***)

let bind #bytes #bl #a #b ps_a ps_b =
  let parse_ab (buf:bytes): option (dtuple2 a b & bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, buf_suffix) -> begin
      match (ps_b xa).parse buf_suffix with
      | None -> None
      | Some (xb, buf_suffix_suffix) -> (
        Some ((|xa, xb|), buf_suffix_suffix)
      )
    end
  in
  let serialize_ab (x:dtuple2 a b): list bytes =
    let (|xa, xb|) = x in
    let la = ps_a.serialize xa in
    let lb = (ps_b xa).serialize xb in
    la@lb
  in

  ({
    parse = parse_ab;
    serialize = serialize_ab;
    parse_serialize_inv = (fun (|xa, xb|) (suffix:bytes) ->
      let la = ps_a.serialize xa in
      let lb = ((ps_b xa).serialize xb) in
      ps_a.parse_serialize_inv xa (add_prefixes lb suffix);
      (ps_b xa).parse_serialize_inv xb suffix;
      add_prefixes_add_prefixes la lb suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_ab buf with
      | None -> ()
      | Some ((|xa, xb|), suffix) ->
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let (xb, suffix) = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv xb_suffix;
        add_prefixes_add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize xb) suffix
    );
  })

let bind_is_not_unit #bytes #bl #a #b ps_a ps_b =
  introduce forall b. length b == 0 ==> (bind ps_a ps_b).parse b == None with (
    match ps_a.parse b with
    | None -> ()
    | Some (xa, b_suffix) ->
      ps_a.serialize_parse_inv b;
      add_prefixes_length (ps_a.serialize xa) b_suffix
  )

let bind_is_well_formed #bytes #bl #a #b ps_a ps_b pre xa xb = ()

let bind_length #bytes #bl #a #b ps_a ps_b xa xb =
  prefixes_length_concat (ps_a.serialize xa) ((ps_b xa).serialize xb)

let isomorphism #bytes #bl #a #b ps_a iso =
  let parse_b buf =
    match ps_a.parse buf with
    | Some (xa, l) -> Some (iso.a_to_b xa, l)
    | None -> None
  in
  let serialize_b xb =
    ps_a.serialize (iso.b_to_a xb)
  in
  let res = {
    parse = parse_b;
    serialize = serialize_b;
    parse_serialize_inv = (fun (x:b) ->
      iso.b_to_a_to_b x;
      ps_a.parse_serialize_inv (iso.b_to_a x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match ps_a.parse buf with
      | Some (xa, l) -> (
        iso.a_to_b_to_a xa;
        ps_a.serialize_parse_inv buf
      )
      | None -> ()
    );
  } in
  res

let isomorphism_is_not_unit #bytes #bl #a #b ps_a iso = ()

let isomorphism_is_well_formed #bytes #bl #a #b ps_a iso pre xb = ()

let isomorphism_length #bytes #bl #a #b ps_a iso xb = ()

let refine #bytes #bl #a ps_a pred =
  {
    parse = (fun buf ->
      match ps_a.parse buf with
      | Some (x, suffix) ->
        if pred x then Some ((x <: refined a pred), suffix)
        else None
      | None -> None
    );
    serialize = (fun x -> ps_a.serialize x);
    parse_serialize_inv = (fun x suffix -> ps_a.parse_serialize_inv x suffix);
    serialize_parse_inv = (fun buf -> ps_a.serialize_parse_inv buf);
  }

let refine_is_not_unit #bytes #bl #a ps_a pred = ()

let refine_is_well_formed #bytes #bl #a ps_a pred pre x = ()

let refine_length #bytes #bl #a ps_a pred x = ()

(*** Parser for basic types ***)

let ps_unit #bytes #bl =
  {
    parse = (fun b -> Some ((), b));
    serialize = (fun _ -> []);
    parse_serialize_inv = (fun _ b -> assert_norm(add_prefixes [] b == b));
    serialize_parse_inv = (fun buf -> assert_norm(add_prefixes [] buf == buf));
  }

let ps_unit_is_well_formed #bytes #bl pre x = assert_norm(for_allP pre [] <==> True)

#push-options "--ifuel 0 --fuel 1"
let ps_unit_length #bytes #bl x = ()
#pop-options

//WHY THE #bytes #bl EVERYWHERE?????
#push-options "--fuel 2"
let ps_lbytes #bytes #bl n =
  let parse_lbytes (buf:bytes): option (lbytes bytes n & bytes) =
    if length buf < n then
      None
    else (
      split_length buf n;
      match split #bytes #bl buf n with
      | Some (x, suffix) -> Some (x, suffix)
      | _ -> None
    )
  in
  let serialize_lbytes (b:lbytes bytes n): list bytes =
    [b]
  in
  empty_length #bytes #bl ();
  {
    parse = parse_lbytes;
    serialize = serialize_lbytes;
    parse_serialize_inv = (fun b suffix ->
      concat_length b suffix;
      split_concat b suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_lbytes buf with
      | None -> ()
      | Some (b, suffix) -> (
        concat_split buf n
      )
    );
  }
#pop-options

let ps_lbytes_is_not_unit #bytes #bl n = ()

let ps_lbytes_is_well_formed #bytes #bl n pre x = assert_norm(for_allP pre [x] <==> pre x)

#push-options "--ifuel 0 --fuel 2"
let ps_lbytes_length #bytes #bl n x = ()
#pop-options

let ps_nat_lbytes #bytes #bl sz =
  let parse_nat_lbytes (buf:bytes): option (nat_lbytes sz & bytes) =
    match (ps_lbytes sz).parse buf with
    | Some (x, suffix) -> (
      match to_nat sz (x <: bytes) with
      | Some n -> Some (n, suffix)
      | None -> None
    )
    | None -> None
  in
  let serialize_nat_lbytes (n:nat_lbytes sz): list bytes =
    (ps_lbytes sz).serialize (from_nat sz n <: bytes)
  in
  {
    parse = parse_nat_lbytes;
    serialize = serialize_nat_lbytes;
    parse_serialize_inv = (fun n suffix ->
      from_to_nat #bytes sz n;
      (ps_lbytes sz).parse_serialize_inv (from_nat sz n <: bytes) suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      (ps_lbytes sz).serialize_parse_inv buf;
      match (ps_lbytes sz).parse buf with
      | Some (x, suffix) -> to_from_nat #bytes sz x
      | None -> ()
    );
  }

let ps_nat_lbytes_is_not_unit #bytes #bl n = ()

let ps_nat_lbytes_is_well_formed #bytes #bl sz pre x = assert_norm(for_allP pre [from_nat sz x] <==> pre (from_nat sz x))

let ps_nat_lbytes_length #bytes #bl sz x = ()

(*** Exact parsers ***)

let ps_to_pse #bytes #bl #a ps_a =
  let parse_exact_a (buf:bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (x, suffix) ->
      if recognize_empty suffix then
        Some x
      else
        None
  in
  let serialize_exact_a (x:a): bytes =
    ps_a.parse_serialize_inv x empty;
    add_prefixes (ps_a.serialize x) empty
  in
  {
    parse_exact = parse_exact_a;
    serialize_exact = serialize_exact_a;
    parse_serialize_inv_exact = (fun x ->
      ps_a.parse_serialize_inv x empty;
      empty_length #bytes ()
    );
    serialize_parse_inv_exact = (fun buf ->
      match parse_exact_a buf with
      | None -> ()
      | Some _ -> (
        let (x, suffix) = Some?.v (ps_a.parse buf) in
        ps_a.serialize_parse_inv buf
      )
    );
  }

let ps_to_pse_is_well_formed #bytes #bl #a ps_a pre x =
  introduce is_well_formed_exact (ps_to_pse ps_a) pre x ==> is_well_formed_partial ps_a pre x
  with _. (
    pre_add_prefixes_to_for_allP_pre #bytes #bl pre (ps_a.serialize x) empty
  );
  introduce is_well_formed_partial ps_a pre x ==> is_well_formed_exact (ps_to_pse ps_a) pre x
  with _. (
    for_allP_pre_to_pre_add_prefixes #bytes #bl pre (ps_a.serialize x) empty
  )

let ps_to_pse_length #bytes #bl #a ps_a x =
  empty_length #bytes ();
  add_prefixes_length (ps_a.serialize x) empty

//The following functions are defined here because F* can't reason on recursive functions defined inside a function
#push-options "--fuel 1"
val _parse_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> buf:bytes -> Tot (option (list a)) (decreases (length (buf <: bytes)))
let rec _parse_la #bytes #bl #a ps_a buf =
  if recognize_empty buf then (
    Some []
  ) else if length (buf <: bytes) = 0 then (
    None
  ) else (
    match ps_a.parse (buf <: bytes) with
    | None -> None
    | Some (h, suffix) -> begin
      if length suffix >= length (buf <: bytes) then (
        None //Impossible case, but no need to prove it here
      ) else (
        match _parse_la ps_a suffix with
        | None -> None
        | Some t -> Some (h::t)
      )
    end
  )
#pop-options

#push-options "--fuel 1"
val _serialize_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> l:list a -> bytes
let rec _serialize_la #bytes #bl #a ps_a l =
  match l with
  | [] -> empty
  | h::t ->
    add_prefixes (ps_a.serialize h) (_serialize_la ps_a t)
#pop-options

#push-options "--fuel 1"
let pse_list #bytes #bl #a ps_a =
  let parse_la (buf:bytes) = _parse_la ps_a buf in
  let serialize_la (l:list a): bytes = _serialize_la ps_a l in
  let rec parse_serialize_inv_la (l:list a): Lemma (parse_la (serialize_la l) == Some l) =
    match l with
    | [] -> empty_length #bytes ()
    | h::t ->
      ps_a.parse_serialize_inv h (serialize_la t);
      let suffix = (_serialize_la ps_a t) in
      if prefixes_length (ps_a.serialize h) = 0 then (
        empty_length #bytes ();
        ps_a.parse_serialize_inv h empty;
        add_prefixes_length (ps_a.serialize h) empty;
        assert(False)
      ) else (
        empty_length #bytes ();
        add_prefixes_length (ps_a.serialize h) suffix;
        parse_serialize_inv_la t
      )
  in

  let rec serialize_parse_inv_la (buf:bytes): Lemma (ensures (match parse_la buf with | None -> True | Some l -> serialize_la l == buf)) (decreases (length (buf <: bytes))) =
    if recognize_empty buf then (
      ()
    ) else if length (buf <: bytes) = 0 then (
      ()
    ) else (
       match parse_la buf with
       | None -> ()
       | Some l ->
         let (_, suffix) = Some?.v (ps_a.parse buf) in
         ps_a.serialize_parse_inv buf;
         serialize_parse_inv_la suffix
    )
  in
  {
    parse_exact = parse_la;
    serialize_exact = serialize_la;
    parse_serialize_inv_exact = parse_serialize_inv_la;
    serialize_parse_inv_exact = serialize_parse_inv_la;
  }
#pop-options

#push-options "--fuel 1"
let rec pse_list_is_well_formed #bytes #bl #a ps_a pre l =
  // ????????
  assert_norm ((pse_list ps_a).serialize_exact l == _serialize_la ps_a l);
  match l with
  | [] -> ()
  | h::t -> (
    assert_norm ((pse_list ps_a).serialize_exact t == _serialize_la ps_a t);
    introduce is_well_formed_exact (pse_list ps_a) pre l ==> for_allP (is_well_formed_partial ps_a pre) l
    with _. (
      pse_list_is_well_formed ps_a pre t;
      pre_add_prefixes_to_for_allP_pre pre (ps_a.serialize h) (_serialize_la ps_a t)
    );
    introduce for_allP (is_well_formed_partial ps_a pre) l ==> is_well_formed_exact (pse_list ps_a) pre l
    with _. (
      pse_list_is_well_formed ps_a pre t;
      for_allP_pre_to_pre_add_prefixes pre (ps_a.serialize h) (_serialize_la ps_a t)
    )
  )
#pop-options

#push-options "--fuel 1"
let rec pse_list_length #bytes #bl #a ps_a l =
  assert_norm ((pse_list ps_a).serialize_exact l == _serialize_la ps_a l);
  match l with
  | [] -> empty_length #bytes ()
  | h::t ->
    assert_norm ((pse_list ps_a).serialize_exact t == _serialize_la ps_a t);
    add_prefixes_length (ps_a.serialize h) (_serialize_la ps_a t);
    pse_list_length ps_a t
#pop-options

let bind_exact #bytes #bl #a #b ps_a ps_b =
  let parse_exact (buf:bytes): option (dtuple2 a b) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, suffix) -> (
      match (ps_b xa).parse_exact suffix with
      | None -> None
      | Some xb -> Some (|xa, xb|)
    )
  in
  let serialize_exact (x:dtuple2 a b): bytes =
    let (|xa, xb|) = x in
    add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize_exact xb)
  in
  {
    parse_exact = parse_exact;
    serialize_exact = serialize_exact;
    parse_serialize_inv_exact = (fun (|xa, xb|) ->
      let la = ps_a.serialize xa in
      let lb = (ps_b xa).serialize_exact xb in
      ps_a.parse_serialize_inv xa lb;
      (ps_b xa).parse_serialize_inv_exact xb
    );
    serialize_parse_inv_exact = (fun buf ->
      match parse_exact buf with
      | None -> ()
      | Some (|xa, xb|) ->
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let xb = Some?.v ((ps_b xa).parse_exact xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv_exact xb_suffix
    );
  }

let bind_exact_is_well_formed_exact #bytes #bl #a #b ps_a ps_b pre xa xb =
  introduce is_well_formed_exact (bind_exact ps_a ps_b) pre (|xa, xb|) ==> is_well_formed_partial ps_a pre xa /\ is_well_formed_exact (ps_b xa) pre xb
  with _. (
    pre_add_prefixes_to_for_allP_pre pre (ps_a.serialize xa) ((ps_b xa).serialize_exact xb)
  );
  introduce is_well_formed_partial ps_a pre xa /\ is_well_formed_exact (ps_b xa) pre xb ==> is_well_formed_exact (bind_exact ps_a ps_b) pre (|xa, xb|)
  with _. (
    for_allP_pre_to_pre_add_prefixes pre (ps_a.serialize xa) ((ps_b xa).serialize_exact xb)
  )

let isomorphism_exact #bytes #bl #a #b ps_a iso =
  let parse_b (buf:bytes): option b =
    match ps_a.parse_exact buf with
    | Some xa -> Some (iso.a_to_b xa)
    | None -> None
  in
  let serialize_b (xb:b): bytes =
    ps_a.serialize_exact (iso.b_to_a xb)
  in
  {
    parse_exact = parse_b;
    serialize_exact = serialize_b;
    parse_serialize_inv_exact = (fun (x:b) ->
      iso.b_to_a_to_b x;
      ps_a.parse_serialize_inv_exact (iso.b_to_a x)
    );
    serialize_parse_inv_exact = (fun (buf:bytes) ->
      match ps_a.parse_exact buf with
      | Some xa -> (
        iso.a_to_b_to_a xa;
        ps_a.serialize_parse_inv_exact buf
      )
      | None -> ()
    );
  }

let isomorphism_exact_is_well_formed #bytes #bl #a #b ps_a iso pre xb = ()


(*** Parser for variable-length lists ***)

val parser_serializer_exact_to_parser_serializer: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> length_pre:(nat -> bool) -> nat_parser_serializer bytes length_pre -> pse_a:parser_serializer_exact bytes a{forall x. length_pre (length (pse_a.serialize_exact x))} -> parser_serializer bytes a
let parser_serializer_exact_to_parser_serializer #bytes #bl #a length_pre ps_nat pse_a =
  let parse_a (buf:bytes) =
    match ps_nat.parse buf with
    | None -> None
    | Some (sz, suffix) -> begin
      match (ps_lbytes sz).parse suffix with
      | None -> None
      | Some (x_lbytes, suffix2) -> begin
        match pse_a.parse_exact x_lbytes with
        | None -> None
        | Some x_a -> Some (x_a, suffix2)
      end
    end
  in
  let serialize_a (x_a:a): list bytes =
    let x_serialized = pse_a.serialize_exact x_a in
    (ps_nat.serialize (length x_serialized)) @ [x_serialized]
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x_a suffix ->
      let x_serialized = pse_a.serialize_exact x_a in
      let sz = (length x_serialized) in
      ps_nat.parse_serialize_inv sz (add_prefixes [x_serialized] suffix);
      add_prefixes_add_prefixes (ps_nat.serialize sz) [x_serialized] suffix;
      pse_a.parse_serialize_inv_exact x_a;
      (ps_lbytes sz).parse_serialize_inv x_serialized suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_a buf with
      | None -> ()
      | Some (x_a, suffix) ->
        let (sz, suffix) = Some?.v (ps_nat.parse buf) in
        let (x_lbytes, suffix2) = Some?.v ((ps_lbytes sz).parse suffix) in
        let x_a = Some?.v (pse_a.parse_exact x_lbytes) in
        ps_nat.serialize_parse_inv buf;
        (ps_lbytes sz).serialize_parse_inv suffix;
        pse_a.serialize_parse_inv_exact x_lbytes;
        add_prefixes_add_prefixes (ps_nat.serialize sz) [x_lbytes] suffix2
    );
  }

val parser_serializer_exact_to_parser_serializer_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  length_pre:(nat -> bool) -> ps_length:nat_parser_serializer bytes length_pre ->
  pse_a:parser_serializer_exact bytes a{forall x. length_pre (length (pse_a.serialize_exact x))} ->
  pre:bytes_compatible_pre bytes -> x:a -> Lemma
  (is_well_formed_partial (parser_serializer_exact_to_parser_serializer length_pre ps_length pse_a) pre x <==> is_well_formed_exact pse_a pre x)
let parser_serializer_exact_to_parser_serializer_is_well_formed #bytes #bl #a length_pre ps_length pse_a pre x =
  let x_serialized = pse_a.serialize_exact x in
  for_allP_append pre (ps_length.serialize (length x_serialized)) [x_serialized];
  assert(is_well_formed_partial ps_length pre (length x_serialized));
  assert_norm(for_allP pre [x_serialized] <==> pre x_serialized)

val parser_serializer_exact_to_parser_serializer_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  length_pre:(nat -> bool) -> ps_length:nat_parser_serializer bytes length_pre ->
  pse_a:parser_serializer_exact bytes a{forall x. length_pre (length (pse_a.serialize_exact x))} ->
  x:a -> Lemma
  (prefixes_length ((parser_serializer_exact_to_parser_serializer length_pre ps_length pse_a).serialize x) == (prefixes_length (ps_length.serialize (length (pse_a.serialize_exact x)))) + (length (pse_a.serialize_exact x)))
let parser_serializer_exact_to_parser_serializer_length #bytes #bl #a length_pre ps_length pse_a x =
  let x_serialized = pse_a.serialize_exact x in
  prefixes_length_concat (ps_length.serialize (length x_serialized)) [x_serialized];
  assert_norm (prefixes_length [x_serialized] == length x_serialized)

val pse_pre_length_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> pre_length:(nat -> bool) -> parser_serializer_exact bytes (pre_length_bytes bytes pre_length)
let pse_pre_length_bytes #bytes #bl pre_length =
  let parse_bytes (buf:bytes): option (pre_length_bytes bytes pre_length) =
    if pre_length (length (buf <: bytes)) then
      Some buf
    else
      None
  in
  let serialize_bytes (buf:pre_length_bytes bytes pre_length): bytes =
    buf
  in
  {
    parse_exact = parse_bytes;
    serialize_exact = serialize_bytes;
    parse_serialize_inv_exact = (fun _ -> ());
    serialize_parse_inv_exact = (fun _ -> ());
  }

let ps_pre_length_bytes #bytes #bl pre_length ps_length =
  parser_serializer_exact_to_parser_serializer pre_length ps_length (pse_pre_length_bytes pre_length)

let ps_pre_length_bytes_is_well_formed #bytes #bl pre_length ps_length pre x =
  parser_serializer_exact_to_parser_serializer_is_well_formed pre_length ps_length (pse_pre_length_bytes pre_length) pre x

let ps_pre_length_bytes_length #bytes #bl pre_length ps_length x =
  parser_serializer_exact_to_parser_serializer_length pre_length ps_length (pse_pre_length_bytes pre_length) x

val pse_pre_length_list: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> pre_length:(nat -> bool) -> ps_a:parser_serializer bytes a -> parser_serializer_exact bytes (pre_length_list ps_a pre_length)
let pse_pre_length_list #bytes #bl #a pre_length ps_a =
  let pse_la = pse_list ps_a in
  {
    parse_exact = (fun buf ->
      if pre_length (length buf) then
        match pse_la.parse_exact buf with
        | Some x ->
          pse_la.serialize_parse_inv_exact buf;
          Some (x <: pre_length_list ps_a pre_length)
        | None -> None
      else
        None
    );
    serialize_exact = (fun x ->
      (pse_list ps_a).serialize_exact x
    );
    parse_serialize_inv_exact = (fun x ->
      pse_la.parse_serialize_inv_exact x
    );
    serialize_parse_inv_exact = (fun buf -> pse_la.serialize_parse_inv_exact buf);
  }

let ps_pre_length_list #bytes #bl #a pre_length ps_length ps_a =
  parser_serializer_exact_to_parser_serializer pre_length ps_length (pse_pre_length_list pre_length ps_a)

let ps_pre_length_list_is_well_formed #bytes #bl #a pre_length ps_length ps_a pre x =
  parser_serializer_exact_to_parser_serializer_is_well_formed pre_length ps_length (pse_pre_length_list pre_length ps_a) pre x;
  assert(is_well_formed_exact (pse_pre_length_list pre_length ps_a) pre x <==> is_well_formed_exact (pse_list ps_a) pre x)

let ps_pre_length_list_length #bytes #bl #a pre_length ps_length ps_a x =
  parser_serializer_exact_to_parser_serializer_length pre_length ps_length (pse_pre_length_list pre_length ps_a) x

let ps_pre_length_seq #bytes #bl #a pre_length ps_length ps_a =
  FStar.Classical.forall_intro (Seq.lemma_list_seq_bij #a);
  FStar.Classical.forall_intro (Seq.lemma_seq_list_bij #a);
  mk_isomorphism (pre_length_seq ps_a pre_length) (ps_pre_length_list pre_length ps_length ps_a)
    (fun (l:pre_length_list ps_a pre_length) -> Seq.seq_of_list l)
    (fun (s:pre_length_seq ps_a pre_length) -> Seq.seq_to_list s)

let ps_pre_length_seq_is_well_formed #bytes #bl #a pre_length ps_length ps_a pre x = ()

let ps_pre_length_seq_length #bytes #bl #a pre_length ps_length ps_a x = ()

(*** TLS-style length ***)

let ps_tls_nat #bytes #bl r =
  let sz = find_nbytes r.max in
  mk_isomorphism (refined nat (in_range r)) (refine (ps_nat_lbytes sz) (in_range r)) (fun n -> n) (fun n -> n)

let ps_tls_nat_length #bytes #bl r x = ()

(*** Unary-style length ***)

val _parse_nat: #bytes:Type0 -> {| bytes_like bytes |} -> b:bytes -> Tot (option (nat & bytes)) (decreases length b)
let rec _parse_nat #bytes #bl b =
  if length b = 0 then (
    None
  ) else (
    split_length b 1;
    match split #bytes b 1 with
    | None -> None
    | Some (l, r) -> (
      if length l <> 1 then (
        None
      ) else (
        match to_nat #bytes 1 l with
        | None -> None
        | Some l_value -> (
          if l_value = 0 then (
            Some (0, r)
          ) else if l_value = 1 then (
            match _parse_nat r with
            | None -> None
            | Some (result, suffix) -> Some (1+result, suffix)
          ) else (
            None
          )
        )
      )
    )
  )

val _serialize_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat -> list bytes
let rec _serialize_nat #bytes #bl n =
  assert_norm (1 < pow2 (8 `op_Multiply` 1));
  if n = 0 then [from_nat 1 0]
  else ((from_nat 1 1)::(_serialize_nat (n-1)))

#push-options "--fuel 1"
val ps_nat_unary: #bytes:Type0 -> {| bytes_like bytes |} -> parser_serializer bytes nat
let ps_nat_unary #bytes #bl =
  let rec parse_serialize_inv (n:nat) (suffix:bytes): Lemma (_parse_nat (add_prefixes (_serialize_nat n) suffix) == Some (n, suffix)) =
    if n = 0 then (
      assert_norm (add_prefixes #bytes [from_nat 1 0] suffix == concat (from_nat 1 0) suffix);
      concat_length #bytes (from_nat 1 0) suffix;
      split_concat #bytes (from_nat 1 0) suffix;
      split_length (concat #bytes (from_nat 1 0) suffix) 1;
      from_to_nat #bytes 1 0
    ) else (
      parse_serialize_inv (n-1) suffix;
      concat_length #bytes (from_nat 1 1) (add_prefixes (_serialize_nat (n-1)) suffix);
      split_concat #bytes (from_nat 1 1) (add_prefixes (_serialize_nat (n-1)) suffix);
      split_length (concat #bytes (from_nat 1 1) (add_prefixes (_serialize_nat (n-1)) suffix)) 1;
      from_to_nat #bytes 1 1
    )
  in
  let rec serialize_parse_inv (buf:bytes): Lemma (ensures (match _parse_nat buf with | Some (x, suffix) -> buf == add_prefixes (_serialize_nat x) suffix | None -> True)) (decreases length buf) =
    match _parse_nat buf with
    | None -> ()
    | Some (n, suffix) -> (
      let (l, r) = Some?.v (split #bytes buf 1) in
      let l_value = Some?.v (to_nat #bytes 1 l) in
      if l_value = 0 then (
        to_from_nat 1 l;
        concat_split buf 1;
        assert_norm (add_prefixes #bytes [from_nat 1 0] suffix == concat (from_nat 1 0) suffix)
      ) else if l_value = 1 then (
        to_from_nat 1 l;
        concat_split buf 1;
        split_length (concat #bytes l r) 1;
        serialize_parse_inv r
      ) else (
        ()
      )
    )
  in

  {
    parse = _parse_nat;
    serialize = _serialize_nat;
    parse_serialize_inv = parse_serialize_inv;
    serialize_parse_inv = serialize_parse_inv;
  }
#pop-options

#push-options "--fuel 1"
val ps_nat_unary_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} ->
  pre:bytes_compatible_pre bytes -> x:nat ->
  Lemma (is_well_formed_partial ps_nat_unary pre x)
  [SMTPat (is_well_formed_partial ps_nat_unary pre x)]
let rec ps_nat_unary_is_well_formed #bytes #bl pre x =
    assert_norm((ps_nat_unary #bytes).serialize x == _serialize_nat x);
    if x = 0 then (
      assert_norm (for_allP pre (_serialize_nat 0) <==> pre (from_nat 1 0))
    ) else (
      assert_norm((ps_nat_unary #bytes).serialize (x-1) == _serialize_nat (x-1));
      ps_nat_unary_is_well_formed pre (x-1)
    )
#pop-options

open FStar.Mul

// Use a "slow" nat parser to derive a more compact one
val ps_nat_accelerate: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes nat -> parser_serializer bytes nat
let ps_nat_accelerate #bytes #bl ps_nat_slow =
  let nbytes_prefix (n:nat): Pure nat (requires True) (ensures fun res -> (n == 0 /\ res == 0) \/ (pow2 (8 * res) <= n /\ n < pow2 (8 * (res+1)))) = (find_nbytes n) - 1 in
  let nbytes_to_pred (nbytes:nat) (n:nat) = (nbytes = 0 && n = 0) || (pow2 (8 * nbytes)) <= n in
  introduce forall (nbytes:nat) (n:nat_lbytes (nbytes+1)). pow2 (8 * nbytes) <= n ==> nbytes == nbytes_prefix n with (
    if pow2 (8 * nbytes) <= n then (
      let found_nbytes = nbytes_prefix n in
      if nbytes < found_nbytes then (
        Math.Lemmas.pow2_le_compat (8 * found_nbytes) (8 * (nbytes+1));
        assert(False)
      ) else if found_nbytes < nbytes then (
        Math.Lemmas.pow2_le_compat (8 * nbytes) (8 * (found_nbytes+1));
        assert(False)
      ) else (
        ()
      )
    ) else (
      ()
    )
  );
  mk_isomorphism nat
    (
      bind #_ #_ #nat #(fun nbytes -> refined (nat_lbytes (nbytes+1)) (nbytes_to_pred nbytes)) ps_nat_slow (fun nbytes ->
        refine (ps_nat_lbytes (nbytes+1)) (nbytes_to_pred nbytes)
      )
    )
    (fun (|nbytes, n|) -> n)
    (fun n -> (|nbytes_prefix n, n|))

let ps_true_nat #bytes #bl =
  mk_isomorphism (refined nat true_nat_pred) (ps_nat_accelerate ps_nat_unary) (fun n -> n) (fun n -> n)

(*** QUIC-style length ***)

type nat_lbits (sz:nat) = n:nat{n < pow2 sz}

#push-options "--z3rlimit 100 --quake 1/5"
val euclidean_div_uniqueness: b:pos -> q1:nat -> q2:nat -> r1:nat -> r2:nat -> Lemma
  (requires r1 < b /\ r2 < b /\ (q1*b + r1 == q2*b + r2))
  (ensures q1 == q2 /\ r1 == r2)
let rec euclidean_div_uniqueness b q1 q2 r1 r2 =
  if q2 < q1 then (
    euclidean_div_uniqueness b q2 q1 r2 r1
  ) else (
    if q1 = 0 then (
      ()
    ) else (
      euclidean_div_uniqueness b (q1-1) (q2-1) r1 r2
    )
  )
#pop-options

val split_nat_lbits_isomorphism: sz1:nat -> sz2:nat -> isomorphism_between (nat_lbits (sz1+sz2)) (nat_lbits sz1 & nat_lbits sz2)
let split_nat_lbits_isomorphism sz1 sz2 =
  let open FStar.Math.Lemmas in
  introduce forall (n:nat_lbits (sz1+sz2)). n / (pow2 sz2) < pow2 sz1 with (
    lemma_div_lt_nat n (sz1+sz2) sz2
  );
  introduce forall (n1:nat_lbits sz1) (n2:nat_lbits sz2). n1 * (pow2 sz2) + n2 < pow2 (sz1+sz2) with (
    lemma_mult_le_right (pow2 sz2) n1 ((pow2 sz1)-1);
    distributivity_sub_left (pow2 sz1) 1 (pow2 sz2);
    pow2_plus sz1 sz2
  );
  introduce forall (n:nat_lbits (sz1+sz2)). (n / (pow2 sz2)) * (pow2 sz2) + (n % (pow2 sz2)) == n with (
    euclidean_division_definition n (pow2 sz2)
  );
  introduce forall (n1:nat_lbits sz1) (n2:nat_lbits sz2). (n1 * (pow2 sz2) + n2) / (pow2 sz2) == n1 /\ (n1 * (pow2 sz2) + n2) % (pow2 sz2) == n2 with (
    let n = (n1 * (pow2 sz2) + n2) in
    euclidean_division_definition n (pow2 sz2);
    euclidean_div_uniqueness (pow2 sz2) n1 ((n1 * (pow2 sz2) + n2) / (pow2 sz2)) n2 ((n1 * (pow2 sz2) + n2) % (pow2 sz2))
  );
  mk_isomorphism_between #(nat_lbits (sz1+sz2)) #(nat_lbits sz1 & nat_lbits sz2)
    (fun n -> (n / (pow2 sz2), n % (pow2 sz2)))
    (fun (n1, n2) -> n1 * (pow2 sz2) + n2)

val flip_isomorphism: #a:Type -> #b:Type -> isomorphism_between a b -> isomorphism_between b a
let flip_isomorphism #a #b iso =
  {
    a_to_b = iso.b_to_a;
    b_to_a = iso.a_to_b;
    a_to_b_to_a = iso.b_to_a_to_b;
    b_to_a_to_b = iso.a_to_b_to_a;
  }

val concat_nat_lbits_isomorphism: sz1:nat -> sz2:nat -> isomorphism_between (nat_lbits sz1 & nat_lbits sz2) (nat_lbits (sz1+sz2))
let concat_nat_lbits_isomorphism sz1 sz2 =
  flip_isomorphism (split_nat_lbits_isomorphism sz1 sz2)

val split_nat_lbits: #bytes:Type0 -> {|bytes_like bytes|} -> sz1:nat -> sz2:nat -> parser_serializer bytes (nat_lbits (sz1+sz2)) -> parser_serializer bytes (nat_lbits sz1 & nat_lbits sz2)
let split_nat_lbits #bytes #bl sz1 sz2 ps_n =
  isomorphism ps_n (split_nat_lbits_isomorphism sz1 sz2)

val isomorphism_subset: #bytes:Type0 -> {|bytes_like bytes|} -> a:Type -> b:Type -> ps_a:parser_serializer bytes a ->
  a_to_b:(a -> option b) -> b_to_a:(b -> a) ->
  a_to_b_to_a: (xa:a -> squash (match a_to_b xa with | None -> True | Some xb -> xa == b_to_a xb)) ->
  b_to_a_to_b: (xb:b -> squash (a_to_b (b_to_a xb) == Some xb)) ->
  parser_serializer bytes b
let isomorphism_subset #bytes #bl a b ps_a a_to_b b_to_a a_to_b_to_a b_to_a_to_b =
  let a_pred (xa:a) = Some? (a_to_b xa) in
  let iso = Mkisomorphism_between #(refined a a_pred) #b
    (fun xa -> Some?.v (a_to_b xa))
    (fun xb -> b_to_a_to_b xb; (b_to_a xb))
    (fun xa -> a_to_b_to_a xa)
    (fun xb -> b_to_a_to_b xb)
  in
  isomorphism (refine ps_a a_pred) iso

#push-options "--z3rlimit 25"
let ps_quic_nat #bytes #bl =
  let open FStar.Math.Lemmas in
  assert_norm(normalize_term (pow2 62) == pow2 62);
  assert_norm(pow2 2 = 4);
  let loglen_to_rem_nbits (loglen:nat_lbits 2) = (8*((pow2 loglen)-1)) in
  let first_byte_to_len (first_byte:((nat_lbits 2) & (nat_lbits 6))): Pure nat (requires True) (fun res -> res <= 7) =
    let (loglen, b1) = first_byte in
    pow2_le_compat 3 loglen;
    assert_norm(pow2 3 = 8);
    (pow2 loglen)-1
  in
  let first_byte_to_type (first_byte:((nat_lbits 2) & (nat_lbits 6))) =
    nat_lbytes (first_byte_to_len first_byte)
  in
  let first_byte_to_parser (first_byte:((nat_lbits 2) & (nat_lbits 6))): parser_serializer_unit bytes (first_byte_to_type first_byte) =
    let len = first_byte_to_len first_byte in
    ps_nat_lbytes len
  in
  let ps_first_byte = split_nat_lbits #bytes 2 6 (mk_trivial_isomorphism (ps_nat_lbytes 1)) in
  let loglen_property (loglen:nat_lbits 2) (n:quic_nat) =
    n < pow2 (6 + loglen_to_rem_nbits loglen) /\ (loglen <> 0 ==> pow2 (6 + loglen_to_rem_nbits (loglen-1)) <= n)
  in
  let n_to_loglen (n:quic_nat): Pure (nat_lbits 2) (requires True) (ensures fun loglen -> loglen_property loglen n) =
    assert_norm (loglen_to_rem_nbits 0 = 0);
    assert_norm (loglen_to_rem_nbits 1 = 8*1);
    assert_norm (loglen_to_rem_nbits 2 = 8*3);
    assert_norm (loglen_to_rem_nbits 3 = 8*7);
    if n < pow2 (6 + loglen_to_rem_nbits 0) then 0
    else if n < pow2 (6 + loglen_to_rem_nbits 1) then 1
    else if n < pow2 (6 + loglen_to_rem_nbits 2) then 2
    else 3
  in
  let n_to_loglen_unique (loglen:nat_lbits 2) (n:quic_nat): Lemma (requires loglen_property loglen n) (ensures loglen == n_to_loglen n) =
    if loglen < n_to_loglen n then (
      pow2_lt_compat loglen ((n_to_loglen n)-1);
      pow2_lt_compat (6 + loglen_to_rem_nbits ((n_to_loglen n)-1)) (6 + loglen_to_rem_nbits loglen)
    ) else if loglen > n_to_loglen n then (
      pow2_lt_compat (loglen-1) (n_to_loglen n);
      pow2_lt_compat (6 + loglen_to_rem_nbits (loglen-1)) (6 + loglen_to_rem_nbits (n_to_loglen n))
    ) else ()
  in

  let a_to_b (x:(dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type)): option quic_nat =
    let (|first_byte, bn|) = x in
    let (loglen, b1) = first_byte in
    let len = first_byte_to_len first_byte in
    pow2_le_compat 62 (6+8*len);
    let res = (concat_nat_lbits_isomorphism 6 (8*len)).a_to_b (b1, bn) in
    if loglen = 0 || pow2 (6 + loglen_to_rem_nbits (loglen-1)) <= res then (
      Some res
    ) else (
      None
    )
  in
  let b_to_a (n:quic_nat): (dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type) =
    let loglen = n_to_loglen n in
    let (b1, bn) = (concat_nat_lbits_isomorphism 6 (loglen_to_rem_nbits loglen)).b_to_a n in
    (|(loglen, b1), bn|)
  in
  let a_to_b_to_a (xa:(dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type)): squash (match a_to_b xa with | None -> True | Some xb -> xa == b_to_a xb) =
    let (|first_byte, bn|) = xa in
    let (loglen, b1) = first_byte in
    let len = first_byte_to_len first_byte in
    (concat_nat_lbits_isomorphism 6 (loglen_to_rem_nbits loglen)).a_to_b_to_a (b1, bn);
    pow2_le_compat 62 (6+8*len);
    let res = (concat_nat_lbits_isomorphism 6 (8*len)).a_to_b (b1, bn) in
    if loglen = 0 then ()
    else if pow2 (6 + loglen_to_rem_nbits (loglen-1)) <= res then
      n_to_loglen_unique loglen res
    else ()
  in
  let b_to_a_to_b (n:quic_nat): squash (a_to_b (b_to_a n) == Some n) =
    let loglen = n_to_loglen n in
    (concat_nat_lbits_isomorphism 6 (loglen_to_rem_nbits loglen)).b_to_a_to_b n
  in
  isomorphism_subset #bytes #bl (dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type) quic_nat (bind ps_first_byte first_byte_to_parser)
    a_to_b b_to_a
    a_to_b_to_a
    b_to_a_to_b

let ps_quic_nat_length #bytes #bl n =
  assert_norm(pow2 0 == 1);
  assert_norm(pow2 1 == 2);
  assert_norm(pow2 2 == 4);
  assert_norm(pow2 3 == 8)
