import PrimeGen


lemma no_prime_factors_im_no_factors {c:ℕ} -- c is a candidate prime
  (h2lc: 2 ≤ c)                              -- c is at least 2
  (hnpf: ∀ p < c, Nat.Prime p → ¬(p∣c))      -- c has no prime factors
  : Nat.Prime c := by
    have : ∀ m < c, m ∣ c → m=1 := by  -- c has no divisors but 1 and c
      intro m hmc hmdc  -- give names to the above assumptions
      by_contra         -- assume ¬(m=1) and show contradiction
      obtain ⟨p, hpp, hpm⟩ : ∃ p, Nat.Prime p ∧ p ∣ m :=
        Nat.exists_prime_and_dvd ‹m ≠ 1›
      have : p∣c := Nat.dvd_trans hpm hmdc
      have : ¬(p∣c) := by
        have : 0 < c := by linarith
        have : 0 < m := Nat.pos_of_dvd_of_pos hmdc this
        have : p ≤ m := Nat.le_of_dvd this hpm
        have : p < c := by linarith
        exact hnpf p this hpp
      contradiction
    exact Nat.prime_def_lt.mpr ⟨‹2 ≤ c› , this⟩


-- naturals less than C
def nltC (c:NPrime) (n:Nat) : Prop := n < c
-- primes less than C
def pltC (c:NPrime) (p:NPrime) : Prop := p < c
-- natural numbers coprime to some known primes:
def cpks (ks:Set NPrime) (n:Nat) : Prop :=
  n ≥ 2  ∧ ∀ p ∈ ks, ¬(p.val ∣ n)


-- S: the set of "known primes", less than C
def S [PrimeGen α] (x:α) : Set NPrime := { p | p < (C x) }

-- R: the set of "remaining" numbers, coprime to all known primes
-- describe the set of naturals with no prime factors less than some c
def R [PrimeGen α] (x:α) : Set Nat := { n | n ≥ 2 ∧ ∀ p ∈ S x, ¬(p.val ∣ n) }
def rs (c : Nat) : Set Nat := { n : Nat | c ≤ n ∧ ∀ p < c, Nat.Prime p → ¬(p∣n) }

structure PrimeSieveSpec {α : Type u} [PrimeGen α] where
  -- these are tne steps you need to prove:
  -- apostrophe indicates result of the 'next' operation
  hCinR (x:α) : (C x).val ∈ R x             -- C is in R (trivial but maybe useful?)
  hCinS (x:α) : (C x) ∈ S (next x)          -- C is in S'
  hRmin (x:α) : ∀ n ∈ (R x), n ≥ (C x)  -- C is min of R
  hNewC (x:α) : (C $ next x) > (C x) -- C' > C


/--
A PrimeSieve is a PrimeGen that uses a sieve to generate primes.
In practice this means that it somehow models the set of natural
numbers greater than 1 that are coprime to a list of primes, and
then repeatedly:
  - obtains the minimum of this set as the next prime
  - eliminates multiples of the new prime. -/
class PrimeSieve {α : Type} [PrimeGen α] where
  todo : sorry



------- ||| everything below here is probably junk ||| ------------


/-

open PrimeSieveSpec
-- demonstrate that (hS, hR, hMin, hNew) are enough to prove
-- that a sieve generates the next consecutive prime at each step
theorem hs_suffice (α : Type u) [PrimeGen α] [PrimeSieveProSpecPrimeSieveSpec
  (x:α) (x':α) (hnx: x' = next x)
  : (C x').val > (C x).val  -- "we have a new, bigger prime"
  ∧ ¬∃ p:NPrime,   -- "and there is no prime between them"
    ((C x).val<p.val ∧ p.val<(C x').val)
  := by
    apply And.intro
    case left => -- "new bigger prime" is class invariant
      rw[hnx]; apply hNewC
    case right =>
      by_contra ex_p; let ⟨p, hp⟩ := ex_p -- assume p exists.
      have : cpks (S x') (C x').val := hR x' (C x').val $ hCinR x'
      simp[cpks] at this
      have ⟨hc'g2, hc'coprime⟩ := this
      -- if there's a prime between C and C', then
      -- C'
      have h: (C $ next x).val > (C x).val := hNewC x
      rw[←hnx] at h
      have : (C x).val < p.val := sorry
      have : p.val < (C x').val := sorry
      sorry
-/


-- if c is a member of rs c, then c is prime
lemma cprime (c : Nat) (h2: c≥2) (hcrc: c ∈ rs c ) : Nat.Prime c :=  by
  have hh : ∀ p < c, Nat.Prime p → ¬(p∣c) := by
    simp[rs] at hcrc
    exact hcrc
  exact no_prime_factors_im_no_factors h2 hh

-- open Classical
-- noncomputable def least (S : Set Nat) (hex: ∃ n, n ∈ S) : Nat :=
--   Nat.find hex

def least_in (nats : List Nat) (h : nats ≠ []) : Nat :=
  nats.foldr Nat.min (List.head nats h)

-- a prime sieve finds the next prime (N) by looking at R(C) (where C is the
-- "current" prime) and then showing that N is a member of R(N).
-- why does this hold for N and not any other member of R(C)?
-- (well, it holds for all prime members, but being the smallest member is
-- sufficient to show that it's the next prime).
-- but what i have to show is that
-- (n = inf rs c) -> (n ∈ rs n) -> (n is prime)

-- show that 2 is part of rs 2 for initial case
lemma cprime2 : 2 ∈ rs 2 := by
  simp [rs]
  intro p hp hprime
  have h1 : p ≤ 1 := Nat.le_of_lt_succ hp
  have h2 : p ≥ 2 := (Nat.prime_def_lt.mp hprime).left
  have h3 : ¬(p ≤ 1) := not_le_of_gt h2
  contradiction
