import PrimeGen
open PrimeGen

set_option autoImplicit false

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
  C (g:α) : Nat -- the "current" or "candidate" prime
  hSmax  (g:α) : ∀ p ∈ S g, P g ≥ p   -- P is the max of S
  hCinR  (g:α) : C g ∈ R g            -- C is an element of R
  hRmin  (g:α) : ∀ n ∈ R g, C g ≤ n   -- C is min of R
  hCgtP  (g:α) : C g > P g            -- C > P
  hP'C   (g:α) : P' g = C g           -- P' = C
open PrimeSieve


theorem no_skipped_prime (α : Type) [PrimeGen α] [PrimeSieve α] (g:α)
  : ¬ ∃ q:NPrime, P g < q ∧ q < C g := by
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

lemma c_prime (α: Type) [PrimeGen α] [PrimeSieve α] (g:α)
  : Nat.Prime (C g) := by
    set c := C g
    have hfac: ∀ q < C g, Nat.Prime q → ¬ q ∣ c := by
      intro q0 hqc hPq
      set q : NPrime := ⟨q0,hPq⟩
      by_cases hq: q ≤ (P g)
      case pos => -- ¬p∣C because C∈R and that's how R is defined
        have hCinR := PrimeSieve.hCinR g
        unfold R S at hCinR; simp at hCinR
        aesop
      case neg => -- we have P < q and q < C but this can't happen
        have : (P g) < q := by exact Nat.gt_of_not_le hq
        have : (P g) < q ∧ q.val < C g := by aesop
        have := no_skipped_prime α g
        rw[not_exists] at this; specialize this q
        contradiction
    have h2c: 2 ≤ C g := by
      set p := P g
      have : p.val ≥ 2 := by exact Nat.Prime.two_le p.prop
      have : c > p.val := hCgtP g
      omega
    exact no_prime_factors_im_no_factors h2c hfac


-- demonstrate that (hS, hR, hMin, hNew) are enough to prove
-- that a sieve generates the next consecutive prime at each step
-- "we have a new, bigger prime, and there is no prime between them"
theorem hs_suffice (α : Type) [PrimeGen α] [PrimeSieve α] (g:α)
  :  (C g > P g) ∧ (¬∃ q:NPrime, P g < q ∧  q < C g) ∧ (Nat.Prime <| C g):= by
    split_ands
    . exact PrimeSieve.hCgtP g
    · exact no_skipped_prime α g
    · exact c_prime α g
