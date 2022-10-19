module Comparse.Utils

open FStar.Mul

val find_nbytes: n:nat -> Pure pos (requires True)
  (ensures fun res -> (n == 0 /\ res == 1) \/ (pow2 (8 * (res-1)) <= n /\ n < pow2 (8 * res)))
