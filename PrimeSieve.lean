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
  -- S: the set of "known primes", ≤ P
  def S : Set NPrime := { p | p ≤ (P x) }
  -- R: the set of "remaining" numbers, coprime to all known primes
  -- describe the set of naturals with no prime factors less than some c
  def R : Set Nat := { n | n ≥ 2 ∧ ∀ p ∈ (S x), ¬(p.val ∣ n) }
end prime_sieve

/--
A PrimeSieve is a PrimeGen that uses a sieve to generate primes.
In practice, this means that it somehow models the set of natural
numbers greater than 1 that are coprime to a list of known primes,
and then repeatedly:
  - obtains the minimum of this set as the next prime
  - eliminates multiples of the new prime. -/
class PrimeSieve (α : Type) [PrimeGen α] where
  -- P (g:α) : NPrime
  C (g:α) : Nat -- canditate for next prime
  hSmax  (g:α) : ∀ p ∈ S g, P g ≥ p   -- P is the max of S
  hRmin  (g:α) : ∀ n ∈ R g, C g ≤ n   -- C is min of R
  hCgtP  (g:α) : C g > P g            -- C > P
  -- hPltP' (g:α) : P' g > P g := sorry
open PrimeSieve

-- demonstrate that (hS, hR, hMin, hNew) are enough to prove
-- that a sieve generates the next consecutive prime at each step
-- "we have a new, bigger prime, and there is no prime between them"
theorem hs_suffice (α : Type) [PrimeGen α] [PrimeSieve α] (g:α)
  :  (C g > P g)  ∧ (¬∃ q:NPrime, P g < q ∧  q < C g) := by
    apply And.intro
    -- the left side is proven for us by the implementor of the sieve:
    case left => exact PrimeSieve.hCgtP g

    -- for the right side, we must show that no prime q can exist between P and C
    case right : (¬∃ q:NPrime, P g < q ∧  q < C g) := by
      intro ⟨q, ⟨hCltQ, hQltG⟩⟩ -- `intro q` on a ¬∃ goal requires we find a contradiction.

      -- hRmin tells us that that C is the min of the set R.
      have hRmin: ∀n ∈ R g, C g ≤ n := PrimeSieve.hRmin <| g

      -- demonstrating `q ∈ R` would show the contradiction since `q<P` and `P` is min of `R`
      suffices hQinR: q.val ∈ R g from by
        apply hRmin at hQinR
        -- the contradiction is between hqltG:(q < G g) and hQinR:(R g ≤ q)
        -- Lean can't see this for the actual definition, so give it some help:
        have {α:Type} {q:Nat} {g:α} {G:α→Nat} (_:q<G g) (_:G g≤q) : False := by omega
        exact this hQltG hQinR

      -- so now we just show hQinR. q∈R means q≥2 ∧ (¬∃p∈ S g, p∣q)
      -- both of these facts follow immediately from the fact that q is prime,
      -- provided we can *also* show that q itself is not an element of s.

      -- (we'll need these two facts to prove both sides of goal).
      have hqP: Nat.Prime q.val := by unfold NPrime at q; aesop
      have hqgt2: q.val ≥ 2 := by simp[Nat.prime_def_lt] at hqP; omega
      unfold R; constructor
      -- part 1. q ∈ R → q ≥ 2.
      case left := hqgt2
      -- part 2. q ∈ R → ¬∃ p ∈ S, p∣q
      case right: ∀ p ∈ (S g), ¬(p.val ∣ q.val) := by
        intro p hp hpq -- assume p exists and p|q. show a contradiction.
        -- since that p|q and both are prime, it follows that p=q.
        have hpP: Nat.Prime p.val := by unfold NPrime at p; aesop
        have : p = q := by
          have : p.val ≠ 1 := Ne.symm <| Nat.ne_of_lt <| Nat.Prime.one_lt hpP
          have : p.val ∣ q.val ↔ p.val = q.val := by exact Nat.prime_dvd_prime_iff_eq hpP hqP
          symm at this; aesop
        -- this means q∈S
        have : q ∈ (S g) := by aesop
        -- so by hGmax, P g > q
        have hCgeQ: P g ≥ q := by
          apply PrimeSieve.hSmax at this
          exact this
        -- and now the same helper we used before, but in the other direction:
        have {α:Type} {q:Nat} {g:α} {G:α→Nat} (_:q<G g) (_:G g≤q) : False := by omega
        exact this hCltQ hCgeQ


-- Here we reformulate R g without reference to (g : PrimeGen α)
-- And instead just use some natural number c.
def rs (c : Nat) : Set Nat := { n : Nat | c ≤ n ∧ ∀ p < c, Nat.Prime p → ¬(p∣n) }

-- if `c` is a member of `rs c`, then c is prime
-- (not *everything* in `rs c` is prime, and `c` itself might not be in `rs c`)
lemma gPrime (c : Nat) (h2: c≥2) (hcrc: c ∈ rs c ) : Nat.Prime c :=  by
  have hh : ∀ p < c, Nat.Prime p → ¬(p∣c) := by
    simp[rs] at hcrc
    exact hcrc
  exact no_prime_factors_im_no_factors h2 hh

def least_in (nats : List Nat) (h : nats ≠ []) : Nat :=
  nats.foldr Nat.min (List.head nats h)

-- show that 2 is part of rs 2 for initial case
lemma cprime2 : 2 ∈ rs 2 := by
  simp [rs]
  intro p hp hprime
  have h1 : p ≤ 1 := Nat.le_of_lt_succ hp
  have h2 : p ≥ 2 := (Nat.prime_def_lt.mp hprime).left
  have h3 : ¬(p ≤ 1) := not_le_of_gt h2
  contradiction
