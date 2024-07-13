-- RakeSieve uses a rake to implement a prime sieve.
import Rake
import PrimeSieve

structure RakeSieve where
  prop : Nat -> Prop
  rm: RakeMap prop
  p : NPrime               -- the current prime
  c : Nat                  -- the canditate for next prime
  hCinR : c ∈ R p
  hRmin : ∀ r ∈ R p, c ≤ r
  -- Q : Array RakeMap     -- queue of found primes

def RakeSieve.init : RakeSieve :=
  { prop := λ n => True ∧ n ≥ 2,
    rm := idrm.gte 2,
    p := ⟨2, Nat.prime_two⟩,
    c := 3,
    hCinR := by
      -- clearly 3 isn't divisible by 2, so is in r
      dsimp[R]; simp; intro q hq
      have : q.val = 2 := by
        have := q.prop; rw[Nat.prime_def_lt] at this
        have : q.val ≥ 2 := this.left
        have : q.val ≤ 2 := by aesop
        omega
      aesop
    hRmin := by
      -- to show that every number in R 2 is ≥ 3,
      -- show that an r∈R 2 where r<3 leads to a contradiction.
      dsimp[R]; intro r ⟨hr, hrr⟩
      by_contra h; simp_all
      -- r ≥ 2 and r < 3, so r must be 2
      have r2 : r = 2 := by omega
      -- but R 2 means not divisible by primes ≤ 2
      let p2 : NPrime := ⟨2, Nat.prime_two⟩
      -- now we can use hrr to prove ¬2∣2, which is absurd
      specialize hrr p2
      have : p2 ≤ p2 := by
        have : p2.val ≤ p2.val := by aesop
        exact this
      apply hrr at this
      rw[r2] at this
      aesop }

def RakeSieve.next (x : RakeSieve) (hC: Nat.Prime x.c) : RakeSieve :=
  let p := x.c
  let c := p + 1 -- TODO: actual next prime
  let prop := λn => x.prop n ∧ ¬ x.c ∣ n
  let rm := x.rm.rem x.c
  { prop := prop, rm := rm, c := c, p := ⟨p, hC⟩,
    hCinR := sorry,
    hRmin := sorry }

instance : SieveState RakeSieve where
  P x := x.p
  C x := x.c
  next x hC := RakeSieve.next x hC
  hNext := by aesop
open SieveState

instance : PrimeSieve RakeSieve where
  hCinR x := by dsimp[C]; dsimp[P]; exact x.hCinR
  hRmin x := by dsimp[C]; dsimp[P]; exact x.hRmin
