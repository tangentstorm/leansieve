import PrimeGen
open PrimeGen

set_option autoImplicit false

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


section prime_sieve
  variable {α : Type} [PrimeGen α]  (x: α)

  -- S: the set of "known primes", less than C
  def S : Set NPrime := { p | p < (C x) }

  -- R: the set of "remaining" numbers, coprime to all known primes
  -- describe the set of naturals with no prime factors less than some c
  def R : Set Nat := { n | n ≥ 2 ∧ ∀ p ∈ (S x), ¬(p.val ∣ n) }

  def S' : Set NPrime := S <| next x
  def R' : Set Nat := R <| next x
end prime_sieve

/--
A PrimeSieve is a PrimeGen that uses a sieve to generate primes.
In practice, this means that it somehow models the set of natural
numbers greater than 1 that are coprime to a list of known primes,
and then repeatedly:
  - obtains the minimum of this set as the next prime
  - eliminates multiples of the new prime. -/
class PrimeSieve (α : Type) [PrimeGen α] : Prop where
  hRmin  (x:α) : ∀n ∈ R x, C x ≤ n    -- C is min of R
  hCmax  (x:α) : ∀ p ∈ S' x, C x ≥ p  -- C is the max of S'
  hNewC  (x:α) : C x < C' x           -- C < C'

-- demonstrate that (hS, hR, hMin, hNew) are enough to prove
-- that a sieve generates the next consecutive prime at each step
-- "we have a new, bigger prime, and there is no prime between them"
theorem hs_suffice (α : Type) [PrimeGen α] [PrimeSieve α] (x:α)
  :  (C' x > C x)  ∧ (¬∃ p:NPrime, C x < p ∧  p < C' x) := by
    apply And.intro
    -- the left side is proven for us by the implementor of the sieve:
    case left => exact PrimeSieve.hNewC x

    -- for the right side, we must show that no prime q can exist between C and C'
    case right : (¬∃ p:NPrime, C x < p ∧  p < C' x) := by
      intro ⟨q, ⟨hCltQ, hQltC'⟩⟩ -- `intro q` on a ¬∃ goal requires we find a contradiction.

      -- hRmin tells us that that C' is the min of the set R'.
      have hR'min: ∀n ∈ R' x, C' x ≤ n := PrimeSieve.hRmin <| next x

      -- demonstrating Q ∈ R' would show the contradiction since Q < C' and C' is min of R
      suffices hQinR': q.val ∈ R' x from by
        apply hR'min at hQinR'; simp_all
        -- the contradiction is between hqltC':(q < C'x) and hQinR':(C'x ≤ q)
        -- Lean can't see this for the actual definition, so give it some help:
        have {α : Type} {q :Nat} {x :α} {C':α→Nat} (lt: q< C' x) (hge: C' x ≤ q) : False := by omega
        exact this hQltC' hQinR'

      -- so now we just show hQinR'. q∈R' means q≥2 ∧ (¬∃p∈ S x, p∣q)
      -- both of these facts follow immediately from the fact that q is prime,
      -- provided we can *also* show that q itself is not an element of s.

      -- (we'll need these two facts to prove both sides of goal).
      have hqP: Nat.Prime q.val := by unfold NPrime at q; aesop
      have hqgt2: q.val ≥ 2 := by simp[Nat.prime_def_lt] at hqP; omega
      unfold R'; constructor
      -- part 1. q ∈ R' → q ≥ 2.
      case left := hqgt2
      -- part 2. q ∈ R' → ¬∃ p ∈ S', p∣q
      case right: ∀ p ∈ (S' x), ¬(p.val ∣ q.val) := by
        intro p hp hpq -- assume p exists and p|q. show a contradiction.
        -- since that p|q and both are prime, it follows that p=q.
        have hpP: Nat.Prime p.val := by unfold NPrime at p; aesop
        have : p = q := by
          have : p.val ≠ 1 := Ne.symm <| Nat.ne_of_lt <| Nat.Prime.one_lt hpP
          have : p.val ∣ q.val ↔ p.val = q.val := by exact Nat.prime_dvd_prime_iff_eq hpP hqP
          symm at this; aesop
        -- this means q∈S'
        have : q ∈ (S' x) := by aesop
        -- so by hCmax, C x > q
        have hCgeQ: C x ≥ q := by
          apply PrimeSieve.hCmax at this
          exact this
        -- and now the same helper we used before, but in the other direction:
        have {α : Type} {q :Nat} {x :α} {C':α→Nat} (lt: q< C' x) (hge: C' x ≤ q) : False := by omega
        exact this hCltQ hCgeQ


--- !! with the above formulation, we still have to prove that C is prime.
-- the code below would let us define C:Nat instead, and derive the fact
-- that C is prime automatically.

-- Here we reformulate R x without reference to (x : PrimeGen α)
-- And instead just use some natural number c.
def rs (c : Nat) : Set Nat := { n : Nat | c ≤ n ∧ ∀ p < c, Nat.Prime p → ¬(p∣n) }

-- if `c` is a member of `rs c`, then c is prime
-- (not *everything* in `rs c` is prime, and `c` itself might not be in `rs c`)
lemma cprime (c : Nat) (h2: c≥2) (hcrc: c ∈ rs c ) : Nat.Prime c :=  by
  have hh : ∀ p < c, Nat.Prime p → ¬(p∣c) := by
    simp[rs] at hcrc
    exact hcrc
  exact no_prime_factors_im_no_factors h2 hh

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
