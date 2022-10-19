module Comparse.Utils

val find_nbytes_aux: n:pos -> acc:pos -> Pure pos (requires pow2 (8 * (acc-1)) <= n)
  (ensures fun res -> pow2 (8 * (res-1)) <= n /\ n < pow2 (8 * res))
  (decreases n - pow2 (8 * (acc-1)))
let rec find_nbytes_aux n acc =
  if n < pow2 (8* acc) then
    acc
  else (
    Math.Lemmas.pow2_lt_compat (8 * acc) (8 * (acc-1));
    find_nbytes_aux n (acc+1)
  )

let find_nbytes n =
  if n = 0 then 1
  else (
    assert_norm(pow2 (8*0) == 1);
    find_nbytes_aux n 1
  )
