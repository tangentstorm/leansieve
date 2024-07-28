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

def rem (rm : RakeMap prop) (x: Nat)
  : RakeMap (λ n => prop n ∧ ¬(x∣n)) :=
  let r₀ := rm.rake
  let r₁ := r₀.rem x
  have hbij₀ : ∀ n, prop n ∧ ¬(x∣n) ↔ ∃ m, r₁.term m = n := by
    intro n
    have hb := rm.hbij
    have hd := r₀.rem_drop x n
    have hk := r₀.rem_keep x n
    have hs := r₀.rem_same x n
    apply Iff.intro; by_cases x∣n; all_goals aesop
  let r₂ := r₁.sort
  let hbij₂ : ∀ n, prop n ∧ ¬(x∣n) ↔ ∃ m, r₂.val.term m = n := by
    intro n
    have hs := r₁.sort_term_iff_term n
    apply Iff.intro; all_goals aesop
  { rake := r₂, hbij := hbij₂, hord := r₂.prop }
