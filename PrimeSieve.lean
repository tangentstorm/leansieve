import PrimeGen

set_option autoImplicit false

class SieveState (α : Type) where
  P     (s:α) : NPrime
  C     (s:α) : Nat
  next  (s:α) (hC: Nat.Prime (C s)) : α
  hNext (s:α) (hC: Nat.Prime (C s)) : (P (next s hC) = C s)
open SieveState

-- R: the "residue", or "remaining" nats coprime to all primes < p.
-- In a sieve, these are the numbers that haven't yet been "sifted out."
def R (P:NPrime): Set Nat := { n | n ≥ 2 ∧ ∀ p ≤ P, ¬(p.val ∣ n) }

-- a simpler version because using NPrime in a proofs tends to require
-- quite a bit of unwrapping and re-wrapping.
def R'(P:Nat) : Set Nat := { n | n≥2 ∧ ∀q≤P, Nat.Prime q → ¬q∣n }

lemma nprime_ge_2 (p:NPrime) : p ≥ (2:Nat) := by
  have := p.prop
  rw[Nat.prime_def_lt] at this
  exact this.left

-- equivalence proof between R and R', with way too much of
-- the aforementioned unwrapping and rewrapping.  :)
@[simp] lemma r'simp (P:NPrime) : (R P) = (R' P.val) := by
  unfold R R'
  rw[Set.ext_iff]; intro x
  apply Iff.intro
  all_goals intro hx; simp_all; have ⟨_, hx1⟩ := hx
  all_goals simp_all; intro q hq
  intro hq2
  case mp : ¬ q ∣ x =>
    -- hx1 says that no prime less than P divides x
    -- the p in scope is not a prime. but.. q ≤ P.val
    -- and p has a prime factor f.
    have : q ≠ 1 := by aesop
    obtain ⟨f, ⟨hf0, hf1⟩⟩ := Nat.exists_prime_and_dvd this
    have : 2 ≤ q := Nat.Prime.two_le hq2
    have : 0 < q := by omega
    have : f ≤ q := Nat.le_of_dvd this hf1
    let f': NPrime := ⟨f, hf0⟩
    specialize hx1 f'
    have : f ≤ P.val := by omega
    have : f' ≤ P := by aesop
    have : ¬ f ∣ x := by aesop
    by_contra hqx
    have : f ∣ x := by exact Nat.dvd_trans hf1 hqx
    contradiction
  case mpr : ¬↑q ∣ x =>
    apply hx1 at hq
    exact hq q.prop

/-- everything in R is greater than P. we use this to show C > P later. -/
lemma r_gt_p (α : Type) [SieveState α] (g:α) : (∀r∈R (P g), r > (P g)) := by
  -- argument: R and S together say ∀ p:prime ≤ P, ¬ p∣r
  intro r hrr;  unfold R at hrr
  -- if r is ≤ P, there is a contradiction.
  by_contra h; simp at h
  -- r (like all natural numbers) has a minimum prime factor f
  have : r ≠ 1 := by aesop -- R say r ≥ 2
  obtain ⟨f, hf', hfr⟩ : ∃ f, Nat.Prime f ∧ f ∣ r :=
      Nat.exists_prime_and_dvd ‹r ≠ 1›
  -- from a chain of relationships we can conclude that f≤P...
  have : 0 < r := by exact Nat.zero_lt_of_lt hrr.left
  have : f ≤ r := Nat.le_of_dvd this hfr
  have : f ≤ (P g) := by omega
  let f' : NPrime := ⟨f, hf'⟩
  have : f' ∈ {p | p ≤ P g} := by aesop
  --- but the R says primes≤P won't divide r
  have : ¬ f ∣ r := by aesop
  contradiction -- with hfr


/- if p₁ is the next consecutive prime after p₀ then
  R p₁ = { n:(R p₀) | ¬ p₁∣n }
  This corresponds to the idea that each time you identify
  the next prime in a sieve, you sift out all its multiples. -/
theorem r_next (p₀: Nat) (m: MinPrimeGt p₀) {n:Nat}
  : (n ∈ R' p₀ ∧ ¬↑m.p ∣ n) ↔ (n ∈ R' m.p) := by
    let ⟨h₁,hinc⟩ := m.hpgt; let hmin := m.hmin; set p₁ := m.p
    unfold R'; simp; apply Iff.intro
    all_goals intro hn; apply And.intro; simp_all
    · show ∀ q ≤ p₁, Nat.Prime q → ¬q ∣ n
      intro q hq hq2
      by_cases hq₀: q≤p₀
      case pos => simp_all
      case neg =>
        by_contra hqn
        simp at hq₀
        have : q ≠ 1 := by aesop
        obtain ⟨f, hf', hfq⟩ := Nat.exists_prime_and_dvd ‹q ≠ 1›
        have hmin := m.hmin
        absurd hmin; simp; use f; split_ands
        · show f < m.p
          have : 0 < q := by omega
          have : f ≤ q := by exact Nat.le_of_dvd this hfq
          have : q ≠ p₁ := by aesop
          have : q < p₁ := by omega
          omega
        · exact hf'
        · show p₀ < f
          simp_all
          by_contra h
          have : f ≤ p₀ := by omega
          have : 2 ≤ f := by exact Nat.Prime.two_le hf'
          simp_all
          have : ¬ f ∣ n := by aesop
          have : f ∣ n := by exact Nat.dvd_trans hfq hqn
          contradiction
    · show ∀ q ≤ p₀, Nat.Prime q → ¬q ∣ n
      intro q hq hq2
      have : q ≤ p₁ := by omega
      exact (hn.right q this) hq2
    · show ¬p₁ ∣ n
      simp_all

/- A prime sieve implementation can model `R p` by providing
a bijection between `R p` and its internal data structures.

For RakeSieve, this is exposed to the type system by attaching
a predicate to the internal data structure.

Whatever the sieve does to "sift out" multiples of the next
prime `p₁` is equivalent to the expression  `∧ ¬(p₁∣n)`.

The following theorem allows us to construct a predicate for
membership in `R pₙ` by induction using predicates of this
form at each step. -/
theorem r_next_prop {p₀ n:Nat} {h₀ h₁: Nat → Prop} {m : MinPrimeGt p₀}
  (hh₀: h₀ n ↔ n ∈ R' p₀) (hh₁: h₁ n ↔ h₀ n ∧ ¬(m.p ∣ n))
  : (h₁ n ↔ n ∈ R' m.p) := by
  simp[hh₁, hh₀]
  exact r_next p₀ m

/--
A PrimeSieve is a PrimeGen that uses a SieveState to generate primes.
In practice, this means that it somehow models the set of natural
numbers greater than 1 that are coprime to a list of known primes,
and then repeatedly:
  - obtains the minimum of this set as the next prime
  - eliminates multiples of the new prime. -/
class PrimeSieve (α : Type) [SieveState α] where
  hCinR  (g:α) : C g ∈ R (P g)            -- C is an element of R
  hRmin  (g:α) : ∀ n ∈ R (P g), C g ≤ n   -- C is min of R
open PrimeSieve

theorem c_gt_p (α : Type) [SieveState α] [PrimeSieve α] (g:α) : C g > P g := by
  have := PrimeSieve.hCinR g
  exact r_gt_p α g (C g) this

theorem no_skipped_prime (α : Type) [SieveState α] [PrimeSieve α] (g:α)
  : ¬ ∃ q:NPrime, P g < q ∧ q < C g := by
    intro ⟨q, ⟨hCltQ, hQltG⟩⟩ -- `intro q` on a ¬∃ goal requires we find a contradiction.
    -- hRmin tells us that that C is the min of the set R.
    have hRmin: ∀n ∈ R (P g), C g ≤ n := PrimeSieve.hRmin <| g

    -- demonstrating `q ∈ R` would show the contradiction since `q<P` and `P` is min of `R`
    suffices hQinR: q.val ∈ R (P g) from by
      apply hRmin at hQinR
      -- the contradiction is between hqltG:(q < G g) and hQinR:(R g ≤ q)
      -- Lean can't see this for the actual definition, so give it some help:
      have {α:Type} {q:Nat} {g:α} {G:α→Nat} (_:q<G g) (_:G g≤q) : False := by omega
      exact this hQltG hQinR

    -- so now we just show hQinR. q∈R means q≥2 ∧ (¬∃p∈ S g, p∣q)
    -- both of these facts follow immediately from the fact that q is prime,
    -- provided we can *also* show that q itself is not an element of s.
    unfold R; constructor
    · show q.val ≥ 2
      exact Nat.Prime.two_le q.prop
    · show ∀ p ≤ (P g), ¬(p.val ∣ q.val)
      intro p hp hpq -- assume p exists and p|q. show a contradiction.
      -- since that p|q and both are prime, it follows that p=q.
      have hp': Nat.Prime p.val := p.prop
      have : p = q := by
        have : p.val ≠ 1 := Ne.symm <| Nat.ne_of_lt <| Nat.Prime.one_lt hp'
        have : p.val ∣ q.val ↔ p.val = q.val := by exact Nat.prime_dvd_prime_iff_eq hp' q.prop
        symm at this; aesop
      have hCgeQ: P g ≥ q := by aesop
      -- and now the same helper we used before, but in the other direction:
      have {α:Type} {q:Nat} {g:α} {G:α→Nat} (_:q<G g) (_:G g≤q) : False := by omega
      exact this hCltQ hCgeQ


lemma no_prime_factors_im_no_factors {c:Nat} -- c is a candidate prime
  (h2lc: 2 ≤ c)                              -- c is at least 2
  (hnpf: ∀ p < c, Nat.Prime p → ¬(p∣c))      -- c has no prime factors
  : Nat.Prime c := by
    have : ∀ m < c, m ∣ c → m=1 := by  -- c has no divisors but 1 and c
      intro m hmc hmdc  -- give names to the above assumptions
      by_contra         -- assume ¬(m=1) and show contradiction
      obtain ⟨p, hp', hpm⟩ : ∃ p, Nat.Prime p ∧ p ∣ m :=
        Nat.exists_prime_and_dvd ‹m ≠ 1›
      have : p∣c := Nat.dvd_trans hpm hmdc
      have : ¬(p∣c) := by
        have : 0 < c := by linarith
        have : 0 < m := Nat.pos_of_dvd_of_pos hmdc this
        have : p ≤ m := Nat.le_of_dvd this hpm
        have : p < c := by linarith
        exact hnpf p this hp'
      contradiction
    exact Nat.prime_def_lt.mpr ⟨‹2 ≤ c› , this⟩


theorem c_prime (α: Type) [SieveState α] [PrimeSieve α] (g:α)
  : Nat.Prime (C g) := by
    set c := C g
    have hfac: ∀ q < C g, Nat.Prime q → ¬ q ∣ c := by
      intro q0 hqc hPq
      set q : NPrime := ⟨q0,hPq⟩
      by_cases hq: q ≤ (P g)
      case pos => -- ¬p∣C because C∈R and that's how R is defined
        have hCinR := PrimeSieve.hCinR g
        unfold R at hCinR; simp at hCinR
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
      have : c > p.val := c_gt_p α g
      omega
    exact no_prime_factors_im_no_factors h2c hfac


-- demonstrate that a sieve generates the next consecutive prime at each step.
-- "we have a new, bigger prime, and there is no prime between them".
theorem hs_suffice (α : Type) [SieveState α] [PrimeSieve α] (g:α)
  :  (Nat.Prime (C g)) ∧ (C g > P g) ∧ (¬∃ q:NPrime, P g < q ∧  q < C g) := by
    split_ands
    · exact c_prime α g
    . exact c_gt_p α g
    · exact no_skipped_prime α g
