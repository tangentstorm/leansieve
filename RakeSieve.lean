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
    hCinR := sorry
    hRmin := sorry }

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
