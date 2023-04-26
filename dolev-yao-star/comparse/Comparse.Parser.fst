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

let rec prefixes_length #bytes #bl l =
  match l with
  | [] -> 0
  | h::t -> length h + prefixes_length t

let is_well_formed_prefix_weaken #bytes #bl #a ps_a pre_strong pre_weak x =
  for_allP_eq pre_strong (ps_a.serialize x);
  for_allP_eq pre_weak (ps_a.serialize x)

let is_not_unit #bytes #bl #a ps_a = forall (x:a). 1 <= prefixes_length (ps_a.serialize x)

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

let bind_serialize #bytes #bl #a #b ps_a ps_b xa xb = ()

let bind_is_not_unit #bytes #bl #a #b ps_a ps_b =
  introduce forall x. 1 <= prefixes_length ((bind ps_a ps_b).serialize x) with (
    let (|xa, xb|) = x in
    prefixes_length_concat (ps_a.serialize xa) ((ps_b xa).serialize xb)
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

let isomorphism_serialize #bytes #bl #a #b ps_a iso x = ()

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

let refine_serialize #bytes #bl #a ps_a pred x = ()

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

let ps_unit_serialize #bytes #bl x = ()

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

let ps_lbytes_serialize #bytes #bl n x = ()

let ps_lbytes_is_not_unit #bytes #bl n =
  assert_norm(forall b. prefixes_length ((ps_lbytes #bytes n).serialize b) == n)

let ps_lbytes_is_well_formed #bytes #bl n pre x = assert_norm(for_allP pre [x] <==> pre x)

#push-options "--ifuel 0 --fuel 2"
let ps_lbytes_length #bytes #bl n x = ()
#pop-options

let ps_nat_lbytes #bytes #bl sz =
  let parse_nat_lbytes (buf:bytes): option (nat_lbytes sz & bytes) =
    match (ps_lbytes sz).parse buf with
    | Some (x, suffix) -> (
      match to_nat (x <: bytes) with
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
      | Some (x, suffix) -> to_from_nat #bytes x
      | None -> ()
    );
  }

let ps_nat_lbytes_serialize #bytes #bl sz x = ()

let ps_nat_lbytes_is_not_unit #bytes #bl n = ()

let ps_nat_lbytes_is_well_formed #bytes #bl sz pre x = assert_norm(for_allP pre [from_nat sz x] <==> pre (from_nat sz x))

let ps_nat_lbytes_length #bytes #bl sz x = ()

(*** Whole parsers ***)

let bind_whole #bytes #bl #a #b ps_a ps_b =
  let parse (buf:bytes): option (dtuple2 a b) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, suffix) -> (
      match (ps_b xa).parse suffix with
      | None -> None
      | Some xb -> Some (|xa, xb|)
    )
  in
  let serialize (x:dtuple2 a b): bytes =
    let (|xa, xb|) = x in
    add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize xb)
  in
  {
    parse = parse;
    serialize = serialize;
    parse_serialize_inv = (fun (|xa, xb|) ->
      let la = ps_a.serialize xa in
      let lb = (ps_b xa).serialize xb in
      ps_a.parse_serialize_inv xa lb;
      (ps_b xa).parse_serialize_inv xb
    );
    serialize_parse_inv = (fun buf ->
      match parse buf with
      | None -> ()
      | Some (|xa, xb|) ->
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let xb = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv xb_suffix
    );
  }

let bind_whole_serialize #bytes #bl #a #b ps_a ps_b xa xb = ()

let bind_whole_is_well_formed_whole #bytes #bl #a #b ps_a ps_b pre xa xb =
  introduce is_well_formed_whole (bind_whole ps_a ps_b) pre (|xa, xb|) ==> is_well_formed_prefix ps_a pre xa /\ is_well_formed_whole (ps_b xa) pre xb
  with _. (
    pre_add_prefixes_to_for_allP_pre pre (ps_a.serialize xa) ((ps_b xa).serialize xb)
  );
  introduce is_well_formed_prefix ps_a pre xa /\ is_well_formed_whole (ps_b xa) pre xb ==> is_well_formed_whole (bind_whole ps_a ps_b) pre (|xa, xb|)
  with _. (
    for_allP_pre_to_pre_add_prefixes pre (ps_a.serialize xa) ((ps_b xa).serialize xb)
  )

let isomorphism_whole #bytes #bl #a #b ps_a iso =
  let parse_b (buf:bytes): option b =
    match ps_a.parse buf with
    | Some xa -> Some (iso.a_to_b xa)
    | None -> None
  in
  let serialize_b (xb:b): bytes =
    ps_a.serialize (iso.b_to_a xb)
  in
  {
    parse = parse_b;
    serialize = serialize_b;
    parse_serialize_inv = (fun (x:b) ->
      iso.b_to_a_to_b x;
      ps_a.parse_serialize_inv (iso.b_to_a x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match ps_a.parse buf with
      | Some xa -> (
        iso.a_to_b_to_a xa;
        ps_a.serialize_parse_inv buf
      )
      | None -> ()
    );
  }

let isomorphism_whole_serialize #bytes #bl #a #b ps_a iso x = ()

let isomorphism_whole_is_well_formed #bytes #bl #a #b ps_a iso pre xb = ()

let refine_whole #bytes #bl #a ps_a pred =
  {
    parse = (fun buf ->
      match ps_a.parse buf with
      | Some x ->
        if pred x then Some (x <: refined a pred)
        else None
      | None -> None
    );
    serialize = (fun x -> ps_a.serialize x);
    parse_serialize_inv = (fun x -> ps_a.parse_serialize_inv x);
    serialize_parse_inv = (fun buf -> ps_a.serialize_parse_inv buf);
  }

let refine_whole_serialize #bytes #bl #a ps_a pred x = ()

(*** Conversion between prefix and whole parsers ***)

let ps_prefix_to_ps_whole #bytes #bl #a ps_a =
  let parse_a (buf:bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (x, suffix) ->
      if recognize_empty suffix then
        Some x
      else
        None
  in
  let serialize_a (x:a): bytes =
    add_prefixes (ps_a.serialize x) empty
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x ->
      ps_a.parse_serialize_inv x empty;
      empty_length #bytes ()
    );
    serialize_parse_inv = (fun buf ->
      match parse_a buf with
      | None -> ()
      | Some _ -> (
        let (x, suffix) = Some?.v (ps_a.parse buf) in
        ps_a.serialize_parse_inv buf
      )
    );
  }

let ps_prefix_to_ps_whole_serialize #bytes #bl #a ps_a x = ()

let ps_prefix_to_ps_whole_is_well_formed #bytes #bl #a ps_a pre x =
  introduce is_well_formed_whole (ps_prefix_to_ps_whole ps_a) pre x ==> is_well_formed_prefix ps_a pre x
  with _. (
    pre_add_prefixes_to_for_allP_pre #bytes #bl pre (ps_a.serialize x) empty
  );
  introduce is_well_formed_prefix ps_a pre x ==> is_well_formed_whole (ps_prefix_to_ps_whole ps_a) pre x
  with _. (
    for_allP_pre_to_pre_add_prefixes #bytes #bl pre (ps_a.serialize x) empty
  )

let ps_prefix_to_ps_whole_length #bytes #bl #a ps_a x =
  empty_length #bytes ();
  add_prefixes_length (ps_a.serialize x) empty

let ps_whole_to_bare_ps_prefix #bytes #bl #a len ps_a =
  let parse_a (buf:bytes) =
      match (ps_lbytes len).parse buf with
      | None -> None
      | Some (x_lbytes, suffix) -> begin
        match ps_a.parse x_lbytes with
        | None -> None
        | Some x_a -> Some (x_a, suffix)
      end
  in
  let serialize_a (x_a:a): list bytes =
    let x_serialized = ps_a.serialize x_a in
    [x_serialized]
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x_a suffix ->
      let x_serialized = ps_a.serialize x_a in
      let sz = (length x_serialized) in
      ps_a.parse_serialize_inv x_a;
      (ps_lbytes sz).parse_serialize_inv x_serialized suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_a buf with
      | None -> ()
      | Some (x_a, suffix) ->
        let (x_lbytes, _) = Some?.v ((ps_lbytes len).parse buf) in
        (ps_lbytes len).serialize_parse_inv buf;
        ps_a.serialize_parse_inv x_lbytes
    );
  }

let ps_whole_to_bare_ps_prefix_serialize #bytes #bl #a len ps_a x = ()

#push-options "--fuel 1 --ifuel 0"
let ps_whole_to_bare_ps_prefix_is_not_unit #bytes #bl #a len ps_a = ()
#pop-options

let ps_whole_to_ps_prefix #bytes #bl #a length_pre ps_nat ps_a =
  let b (sz:refined nat length_pre) = refined a (ps_whole_length_pred ps_a sz) in
  mk_isomorphism a
    (bind #bytes #_ #(refined nat length_pre) #b ps_nat (fun sz -> ps_whole_to_bare_ps_prefix sz (refine_whole ps_a (ps_whole_length_pred ps_a sz))))
    (fun (|sz, x|) -> x)
    (fun x -> (|length (ps_a.serialize x), x|))

let ps_whole_to_ps_prefix_serialize #bytes #bl #a length_pre ps_length ps_a x = ()

let ps_whole_to_ps_prefix_is_well_formed #bytes #bl #a length_pre ps_length ps_a pre x =
  let x_serialized = ps_a.serialize x in
  for_allP_append pre (ps_length.serialize (length x_serialized)) [x_serialized];
  assert(is_well_formed_prefix ps_length pre (length x_serialized));
  assert_norm(for_allP pre [x_serialized] <==> pre x_serialized)

let ps_whole_to_ps_prefix_length #bytes #bl #a length_pre ps_length ps_a x =
  let x_serialized = ps_a.serialize x in
  prefixes_length_concat (ps_length.serialize (length x_serialized)) [x_serialized];
  assert_norm (prefixes_length [x_serialized] == length x_serialized)

(*** Whole parsers ***)

let ps_whole_bytes #bytes #bl =
  {
    parse = (fun x -> Some x);
    serialize = (fun x -> x);
    parse_serialize_inv = (fun _ -> ());
    serialize_parse_inv = (fun _ -> ());
  }

let ps_whole_bytes_serialize #bytes #bl b = ()

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
let ps_whole_list #bytes #bl #a ps_a =
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
    parse = parse_la;
    serialize = serialize_la;
    parse_serialize_inv = parse_serialize_inv_la;
    serialize_parse_inv = serialize_parse_inv_la;
  }
#pop-options

#push-options "--fuel 1"
let rec ps_whole_list_serialize #bytes #bl #a ps_a l =
  assert_norm (forall l. (ps_whole_list ps_a).serialize l == _serialize_la ps_a l);
  match l with
  | [] -> ()
  | h::t -> ps_whole_list_serialize ps_a t
#pop-options

#push-options "--fuel 1"
let rec ps_whole_list_is_well_formed #bytes #bl #a ps_a pre l =
  // ????????
  assert_norm (forall l. (ps_whole_list ps_a).serialize l == _serialize_la ps_a l);
  match l with
  | [] -> ()
  | h::t -> (
    introduce is_well_formed_whole (ps_whole_list ps_a) pre l ==> for_allP (is_well_formed_prefix ps_a pre) l
    with _. (
      ps_whole_list_is_well_formed ps_a pre t;
      pre_add_prefixes_to_for_allP_pre pre (ps_a.serialize h) (_serialize_la ps_a t)
    );
    introduce for_allP (is_well_formed_prefix ps_a pre) l ==> is_well_formed_whole (ps_whole_list ps_a) pre l
    with _. (
      ps_whole_list_is_well_formed ps_a pre t;
      for_allP_pre_to_pre_add_prefixes pre (ps_a.serialize h) (_serialize_la ps_a t)
    )
  )
#pop-options

#push-options "--fuel 1"
let rec ps_whole_list_length #bytes #bl #a ps_a l =
  assert_norm (forall l. (ps_whole_list ps_a).serialize l == _serialize_la ps_a l);
  match l with
  | [] -> empty_length #bytes ()
  | h::t ->
    add_prefixes_length (ps_a.serialize h) (_serialize_la ps_a t);
    ps_whole_list_length ps_a t
#pop-options

#push-options "--fuel 1"
val list_unrefb: #a:Type -> #p:(a -> bool) -> list (x:a {p x}) -> l:list a {List.Tot.for_all p l}
let rec list_unrefb #a #p l =
  match l with
  | [] -> []
  | h::t -> h::(list_unrefb t)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val list_refb_unrefb:
  #a:eqtype -> #p:(a -> bool) ->
  l:list (x:a {p x}) ->
  Lemma (list_refb #a #p (list_unrefb #a #p l) == l)
let rec list_refb_unrefb #a #p l =
  match l with
  | [] -> (
    assert_norm(list_unrefb #a #p (list_refb #a #p []) == [])
  )
  | h::t -> (
    list_refb_unrefb #a #p t;
    assert_norm(list_refb #a #p (list_unrefb #a #p (h::t)) == h::(list_refb #a #p (list_unrefb #a #p t)))
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val list_unrefb_refb:
  #a:eqtype -> #p:(a -> bool) ->
  l:list a{for_all p l} ->
  Lemma (list_unrefb #a #p (list_refb #a #p l) == l)
let rec list_unrefb_refb #a #p l =
  match l with
  | [] -> ()
  | h::t -> list_unrefb_refb #a #p t
#pop-options

#push-options "--ifuel 1 --fuel 1"
val isomorphism_between_list: #a:Type -> #b:Type -> isomorphism_between a b -> isomorphism_between (list a) (list b)
let isomorphism_between_list #a #b iso =
  let a_to_b (l:list a): list b = List.Tot.map iso.a_to_b l in
  let b_to_a (l:list b): list a = List.Tot.map iso.b_to_a l in
  let rec a_to_b_to_a (l:list a): squash (b_to_a (a_to_b l) == l) =
    match l with
    | [] -> ()
    | h::t -> (
      iso.a_to_b_to_a h;
      a_to_b_to_a t
    )
  in
  let rec b_to_a_to_b (l:list b): squash (a_to_b (b_to_a l) == l) =
    match l with
    | [] -> ()
    | h::t -> (
      iso.b_to_a_to_b h;
      b_to_a_to_b t
    )
  in
  {
    a_to_b;
    b_to_a;
    a_to_b_to_a;
    b_to_a_to_b;
  }
#pop-options

let ps_whole_ascii_string #bytes #bl =
  let ascii_string_nonorm = s:string{string_is_ascii s} in
  let list_char_is_ascii (l: list FStar.Char.char) = List.Tot.for_all char_is_ascii l in
  let list_ascii_char = l: list FStar.Char.char{list_char_is_ascii l} in
  let ps_list_ascii_char =
    isomorphism_whole (ps_whole_list #bytes (ps_nat_lbytes 1)) (
      isomorphism_between_list {
        a_to_b = (fun (x:nat_lbytes 1) -> (FStar.Char.char_of_int x <: (c:FStar.Char.char{char_is_ascii c})));
        b_to_a = ascii_char_to_byte;
        a_to_b_to_a = (fun x -> FStar.Char.u32_of_char_of_u32 (FStar.UInt32.uint_to_t x));
        b_to_a_to_b = (fun x -> FStar.Char.char_of_u32_of_char x);
      }
    )
  in
  let ps_list_ascii_char' =
    mk_trivial_isomorphism_whole (
      isomorphism_whole ps_list_ascii_char ({
        a_to_b = (fun (x:list (c:FStar.Char.char{char_is_ascii c})) ->
          list_unrefb #FStar.Char.char #char_is_ascii x
        );
        b_to_a = (fun (x:list_ascii_char) ->
          list_refb #FStar.Char.char #char_is_ascii x
        );
        a_to_b_to_a = (fun x -> list_refb_unrefb #FStar.Char.char #char_is_ascii x);
        b_to_a_to_b = (fun x -> list_unrefb_refb #FStar.Char.char #char_is_ascii x);
      })
    )
  in
  let ps_ascii_string_nonorm =
    isomorphism_whole ps_list_ascii_char' ({
      a_to_b = (fun (x:list_ascii_char) ->
        FStar.String.list_of_string_of_list x;
        (FStar.String.string_of_list x) <: ascii_string_nonorm
      );
      b_to_a = (fun (x:ascii_string_nonorm) ->
        FStar.String.list_of_string x
      );
      a_to_b_to_a = (fun x -> FStar.String.list_of_string_of_list x);
      b_to_a_to_b = (fun x -> FStar.String.string_of_list_of_string x);
    })
  in
  assert_norm(forall x. string_is_ascii x <==> normalize_term (b2t (string_is_ascii x)));
  mk_trivial_isomorphism_whole ps_ascii_string_nonorm

#push-options "--fuel 1 --ifuel 1"
let ps_whole_ascii_string_serialize #bytes #bl x =
  assert_norm ((ps_whole_ascii_string #bytes).serialize x ==
    (ps_whole_list (ps_nat_lbytes 1)).serialize (
      List.Tot.map ascii_char_to_byte (List.Tot.list_refb #_ #char_is_ascii (FStar.String.list_of_string x))
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
let ps_whole_ascii_string_length #bytes #bl x =
  let rec lem (l:list (nat_lbytes 1)): Lemma (bytes_length #bytes (ps_nat_lbytes 1) l == List.Tot.length l) =
    match l with
    | [] -> ()
    | h::t -> lem t
  in
  ps_whole_ascii_string_serialize #bytes x;
  let the_list = (List.Tot.map ascii_char_to_byte (List.Tot.list_refb #_ #char_is_ascii (FStar.String.list_of_string x))) in
  ps_whole_list_length #bytes (ps_nat_lbytes 1) the_list;
  lem the_list
#pop-options

(*** Parser for variable-length lists ***)

val ps_whole_pre_length_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> pre_length:(nat -> bool) -> parser_serializer_whole bytes (pre_length_bytes bytes pre_length)
let ps_whole_pre_length_bytes #bytes #bl pre_length =
  let length_pred (x:bytes) = pre_length (length (ps_whole_bytes.serialize x)) in
  mk_trivial_isomorphism_whole (refine_whole ps_whole_bytes length_pred)

let ps_pre_length_bytes #bytes #bl pre_length ps_length =
  ps_whole_to_ps_prefix pre_length ps_length (ps_whole_pre_length_bytes pre_length)

let ps_pre_length_bytes_serialize #bytes #bl pre_length ps_length x =
  ps_whole_to_ps_prefix_serialize pre_length ps_length (ps_whole_pre_length_bytes pre_length) x

let ps_pre_length_bytes_is_well_formed #bytes #bl pre_length ps_length pre x =
  ps_whole_to_ps_prefix_is_well_formed pre_length ps_length (ps_whole_pre_length_bytes pre_length) pre x

let ps_pre_length_bytes_length #bytes #bl pre_length ps_length x =
  ps_whole_to_ps_prefix_length pre_length ps_length (ps_whole_pre_length_bytes pre_length) x

val ps_whole_pre_length_list: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> pre_length:(nat -> bool) -> ps_a:parser_serializer bytes a -> parser_serializer_whole bytes (pre_length_list ps_a pre_length)
let ps_whole_pre_length_list #bytes #bl #a pre_length ps_a =
  let length_pred (x:list a) = pre_length (length ((ps_whole_list ps_a).serialize x)) in
  mk_trivial_isomorphism_whole (refine_whole (ps_whole_list ps_a) length_pred)

let ps_pre_length_list #bytes #bl #a pre_length ps_length ps_a =
  ps_whole_to_ps_prefix pre_length ps_length (ps_whole_pre_length_list pre_length ps_a)

let ps_pre_length_list_serialize #bytes #bl #a pre_length ps_length ps_a x =
  ps_whole_to_ps_prefix_serialize pre_length ps_length (ps_whole_pre_length_list pre_length ps_a) x

let ps_pre_length_list_is_well_formed #bytes #bl #a pre_length ps_length ps_a pre x =
  ps_whole_to_ps_prefix_is_well_formed pre_length ps_length (ps_whole_pre_length_list pre_length ps_a) pre x;
  assert(is_well_formed_whole (ps_whole_pre_length_list pre_length ps_a) pre x <==> is_well_formed_whole (ps_whole_list ps_a) pre x)

let ps_pre_length_list_length #bytes #bl #a pre_length ps_length ps_a x =
  ps_whole_to_ps_prefix_length pre_length ps_length (ps_whole_pre_length_list pre_length ps_a) x

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
  mk_trivial_isomorphism (refine (ps_nat_lbytes sz) (in_range r))

#push-options "--fuel 1"
let ps_tls_nat_serialize #bytes #bl r x = ()
#pop-options

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
        match to_nat #bytes l with
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
      split_concat #bytes (from_nat 1 0) suffix;
      split_length (concat #bytes (from_nat 1 0) suffix) 1;
      from_to_nat #bytes 1 0
    ) else (
      parse_serialize_inv (n-1) suffix;
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
      let l_value = Some?.v (to_nat #bytes l) in
      if l_value = 0 then (
        to_from_nat l;
        concat_split buf 1;
        assert_norm (add_prefixes #bytes [from_nat 1 0] suffix == concat (from_nat 1 0) suffix)
      ) else if l_value = 1 then (
        to_from_nat l;
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
  Lemma (is_well_formed_prefix ps_nat_unary pre x)
  [SMTPat (is_well_formed_prefix ps_nat_unary pre x)]
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

#push-options "--fuel 0 --ifuel 0 --z3cliopt smt.arith.nl=false"
val euclidean_div_uniqueness: b:pos -> q1:nat -> q2:nat -> r1:nat -> r2:nat -> Lemma
  (requires r1 < b /\ r2 < b /\ (q1*b + r1 == q2*b + r2))
  (ensures q1 == q2 /\ r1 == r2)
let rec euclidean_div_uniqueness b q1 q2 r1 r2 =
  if q2 < q1 then (
    euclidean_div_uniqueness b q2 q1 r2 r1
  ) else (
    if q1 = 0 then (
      FStar.Math.Lemmas.mul_zero_left_is_zero b;
      if 1 <= q2 then (
        FStar.Math.Lemmas.lemma_mult_le_right b 1 q2;
        assert(False)
      ) else ()
    ) else (
      FStar.Math.Lemmas.distributivity_sub_left q1 1 b;
      FStar.Math.Lemmas.distributivity_sub_left q2 1 b;
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
  let first_byte_to_parser (first_byte:((nat_lbits 2) & (nat_lbits 6))): parser_serializer_prefix bytes (first_byte_to_type first_byte) =
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
