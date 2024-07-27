import Rake

/--
A RakeMap is a Rake that provides a 1-to-1 mapping between the rake
and a set of numbers with some property. -/
structure RakeMap (pred: Nat → Prop) where
  rake : Rake
  hbij : ∀ n, pred n ↔ ∃ m, rake.term m = n
  hord : rake.sorted := by rfl

namespace RakeMap

open Rake

def term (rm: RakeMap p) (n:Nat) := rm.rake.term n

theorem min_term_zero (rm:RakeMap p)  : ∀ n, (rm.term 0 ≤ rm.term n) :=
  @Rake.sorted_min_term_zero rm.rake rm.hord

def pred {p:Nat → Prop} (_:RakeMap p) : Nat → Prop := p

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

section rem_lemmas

  -- now it's more complicated. first we partition each sequence
  -- then we remove the sequences that are multiples of a prime
  -- how do we know:
  --   - we dropped the multiples?
  --     - partition step keeps same terms
  --     - but now every sequence either ALWAYS or NEVER produces multiples of p
  --     - we can tell the difference, and only drop the ones that always produce multiples
  --   - we know we kept everything else because it's a straight filter operation.


  variable (rm: RakeMap prop) (p n: Nat) {hp: 0<p}

  lemma rem_drop -- rem drops multiples of p
    : p∣n → ¬(∃m, (rm.rake.rem p).sort.val.term m = n) := by
    sorry

  lemma rem_keep -- rem keeps non-multiples of p
    : ¬(p∣n) ∧ (∃pm, rm.rake.term pm = n) → (∃m, (rm.rake.rem p).sort.val.term m = n) := by
    sorry

  lemma rem_same -- rem introduces no new terms
    : (∃m, (rm.rake.rem p).sort.val.term m = n) → (∃pm, rm.rake.term pm = n) := by
    sorry

end rem_lemmas

-- operations on RakeMap -------------------------------------------------------

-- def RakeMap.sort (rm: RakeMap prop) : RakeMap prop // }

def rem (rm : RakeMap prop) (p: Nat)
  : RakeMap (λ n => prop n ∧ ¬(p∣n)) :=
  let rake := (rm.rake.rem p).sort
  let proof := by
    intro n; symm
    let hm : Prop := (∃m, rake.val.term m = n)
    let hpm : Prop := (∃pm, rm.rake.term pm = n )
    have : prop n ↔ hpm := rm.hbij n
    have : p∣n → ¬hm := rem_drop rm p n
    have : ¬p∣n ∧ hpm → hm := rem_keep rm p n
    have : hm → hpm := rem_same rm p n
    by_cases p∣n; all_goals aesop
  { rake := rake, hbij := proof, hord := rake.prop }
