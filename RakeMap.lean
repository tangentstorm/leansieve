import Rake

/--
A RakeMap provides a 1-to-1 mapping between its rake
and a set of numbers with some property. -/
structure RakeMap (pred: Nat → Prop) where
  rake : Rake
  hbij : ∀ n, pred n ↔ ∃ m, rake.term m = n
  hord : rake.sorted := by rfl

namespace RakeMap

open Rake

def pred {p:Nat → Prop} (_:RakeMap p) : Nat → Prop := p
def term (rm: RakeMap p) (n:Nat) := rm.rake.term n

theorem min_term_zero (rm:RakeMap p)  : ∀ n, (rm.term 0 ≤ rm.term n) :=
  @Rake.sorted_min_term_zero rm.rake rm.hord

/-- proof that rm_nat.term provides a bijection from Nat → Nat
 (it happens to be an identity map, but this is not necessary for proofs) -/
def rm_nat : RakeMap (λ _ => True) := {
  rake := nat
  hbij := by intro n; simp[Rake.term, nat, aseq, ASeq.term]}

def rm_ge2 : RakeMap (λn => 2≤n) := {
  rake := ge2
  hbij := by
    intro n; simp[Rake.term, ge2, aseq, ASeq.term]; apply Iff.intro
    · show 2 ≤ n → ∃ m, 2 + m = n
      intro n2; use n-2; simp_all
    · show (∃ m, 2 + m = n) → 2 ≤ n
      intro hm; obtain ⟨m,hm⟩ := hm; rw[←hm]; simp }

-- operations on RakeMap -------------------------------------------------------

/-
This removes all multiples of a number from the rake.
- `hx: 0 < x` is necessary because we multiply the delta
  by x in the partition step, and delta=0 gives you a cyclic rake.
- `h0: ¬ prop 0` is something of a hack: we have to do *something*
  if every term in the rake is a multiple of x. We can't allow
  `.ks=[]` because that would make `.term` meaningless. We *could*
  have `rem` return `Option Rake`, but then you'd have to test for
  it. Or we could force the callet to provide a proof of
  `∃m n, r.term m = n ∧ ¬n∣div`

-/
def rem (rm : RakeMap prop) (x: Nat) (hx: 0<x) (h0: ¬prop 0)
  : RakeMap (λ n => (prop n ∧ ¬(x∣n))) :=
  let r₀ := rm.rake
  let r₁ := r₀.rem x hx
  have hbij₀ := r₀.hbij
  have hbij₁ : ∀n, (prop n ∧ ¬(x∣n) ↔ ∃ m, r₁.term m = n) := by
    intro n
    by_cases hn: 0<n
    have hb := rm.hbij
    have hd := r₀.rem_drop x n hx hn
    have hk := r₀.rem_keep x n hx
    have ¬∃m, r₀.term m = 0 := by sorry
    have hs := r₀.rem_same x n hx h0
    all_goals apply Iff.intro; by_cases x∣n
    -- aesop can handle 5 of the 6 goals:
    aesop; aesop; aesop; aesop; aesop
    -- aesop needs some help with the last case:
    show (∃ m, r₁.term m = n) → prop n ∧ ¬x ∣ n
    sorry
  let r₂ := r₁.sort
  let hbij₂ : ∀ n, prop n ∧ ¬(x∣n) ↔ ∃ m, r₂.val.term m = n := by
    intro n
    have hs := r₁.sort_term_iff_term n
    apply Iff.intro; all_goals aesop
  { rake := r₂, hbij := hbij₂, hord := by simp[r₂.prop] }
