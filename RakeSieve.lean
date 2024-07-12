-- RakeSieve uses a rake to implement a prime sieve.
import Rake
import PrimeSieve

structure RakeSieve where
  prop : Nat -> Prop
  rm: RakeMap prop
  p : NPrime
  c : Nat                  -- the canditate for next prime
  -- Q : Array Nat         -- queue of found primes

def RakeSieve.init : RakeSieve :=
  { prop := λ n => True ∧ n ≥ 2,
    rm := idrm.gte 2,
    p := ⟨2, Nat.prime_two⟩,
    c := 3}

def RakeSieve.next (x : RakeSieve) (hC: Nat.Prime x.c) : RakeSieve :=
  let p := x.c
  let c := p + 1 -- TODO: actual next prime
  let prop := λn => x.prop n ∧ ¬ x.c ∣ n
  let rm := x.rm.rem x.c
  { prop := prop, rm := rm, c := c, p := ⟨p, hC⟩ }

instance : SieveState RakeSieve where
  P x := x.p
  C x := x.c
  next x hC := RakeSieve.next x hC
  hNext := by aesop

open SieveState

theorem RakeSieve.hCinR  (g:RakeSieve) : C g ∈ R g            -- C is an element of R
  := sorry
theorem RakeSieve.hRmin  (g:RakeSieve) : ∀ n ∈ R g, C g ≤ n   -- C is min of R
  := sorry
theorem RakeSieve.hCgtP  (g:RakeSieve) : C g > P g            -- C > P
  := sorry

instance : PrimeSieve RakeSieve where
  hCinR := RakeSieve.hCinR
  hRmin := RakeSieve.hRmin
  hCgtP := RakeSieve.hCgtP
