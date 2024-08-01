import Mathlib.Tactic
-- import Mathlib.Data.Nat.Prime


example {x y:Nat} : Prop := by
  let n := x + 1 -- just any arbitrary definition
  have : n > y := by
    -- goal is n > y and I want to rewrite using the
    -- definition of n:
    -- those two lines work:
    dsimp[n]
    show x + 1 > y
    -- but is there a simpler way?
    sorry
  sorry



variable {m n d k: Nat}  {hdpos: 0 < d}
theorem nat_div_xx₀ : m<n → (m/d < n/d) ≠ ((m/d=n/d) ∧ (m%d < n%d)) := by
  intro hmn
  set q₀ := m/d; set r₀ := m%d
  set q₁ := n/d; set r₁ := n%d
  have hdu₀ := @Nat.div_mod_unique n d r₀ q₀ hdpos
  have hdu₁ := @Nat.div_mod_unique n d r₁ q₁ hdpos
  by_cases h : q₀ < q₁
  case pos => intro hqq; aesop
  case neg =>
    simp[not_iff]
    apply Iff.intro
    case mpr => aesop
    case mp =>
      intro hqq
      simp_all
      apply And.intro
      · show q₀ = q₁
        have : r₀ < d := by exact Nat.mod_lt m hdpos
        have : r₁ < d := by exact Nat.mod_lt n hdpos
        simp_all
        sorry
      · show r₀ < r₁
        sorry

theorem nat_le_mul_div_succ  {hdpos: 0 < d}: n ≤ d * (n/d + 1) := by
  simp[Nat.mul_add]
  conv => left; rw[← Nat.div_add_mod n d]
  have := Nat.mod_lt n hdpos
  omega

@[simp] theorem nat_div_mod : d*(n/d) = (n-n%d):= by
  have : n/d=(n-n%d)/d := by exact Nat.div_eq_sub_mod_div
  have : d∣(n-n%d) := by exact Nat.dvd_sub_mod n
  have : d*((n-n%d)/d) = (n-n%d) := by exact Nat.mul_div_cancel' this
  simp_all only [and_self]

theorem nat_eq_iff_div_mod : m=n ↔ m/d=n/d ∧ m%d=n%d := by
  apply Iff.intro; all_goals intro h
  case mp =>
    split_ands; all_goals subst h; rfl
  case mpr =>
    have hml: m%d ≤ m := by exact Nat.mod_le m d
    have hnl: n%d ≤ n := by exact Nat.mod_le n d
    have : d*(m/d) = d*(n/d) := by aesop
    have : m - m%d + m%d = n - n%d + m%d := by simpa[nat_div_mod]
    have : m             = n - n%d + m%d := by simp_all[Nat.sub_add_cancel]
    omega

theorem div_le_add_div : m/d ≤ (m+k)/d := by
  have : m/d + k/d ≤ (m+k)/d := by exact Nat.add_div_le_add_div m k d
  have : m/d ≤ m/d + k/d := by simp only [le_add_iff_nonneg_right, zero_le]
  omega


syntax "assert" term : command
macro_rules | `(assert $x) => `(example : $x := by decide)

assert 5=5
assert 5=2


def evens (n:Nat) := List.range n |>.map (·*2)
example : evens 4 = [0,2,4,6] := by decide




def NPrime : Type := { n: Nat // Nat.Prime n }
  deriving Repr, Ord, LT, LE

example (p:NPrime) : p.val ≥ 2 := by
  set p' := p.val; have : Nat.Prime p' := p.prop
  exact Nat.Prime.two_le this

-- can't even say this because
def p2 : NPrime := ⟨2, Nat.prime_two⟩
example (p:NPrime) : p ≥ p2 := by exact?

instance : Coe NPrime Nat where coe n := n.val

lemma pgt (p:NPrime) : (p2 ≤ p) := by
  set p2' := p2.val; have : Nat.Prime p2' := p2.prop
  set p' := p.val; have : Nat.Prime p' := p.prop
  -- have : Nat.Prime p := by unfold NPrime at p; aesop
  --  have : 2 ≤ p.val := by simp[Nat.prime_def_lt] at this; omega
  aesop


structure NPStruct (p:NPrime) where
  p': Nat
  pp': p'=p.val
  h: Nat.Prime p
def NPrime.unwrap (p:NPrime) : NPStruct p := ⟨p.val, rfl, p.prop⟩

lemma pgt' (p:NPrime) : (p2 ≤ p) := by
  obtain ⟨p', pp', hp'⟩ := p.unwrap
  have : 2 ≤ p' := by simp[Nat.prime_def_lt] at hp'; omega
  aesop


@[simp] theorem NPrime.eq_iff (a b : NPrime) : a = b ↔ a.val = b.val := Subtype.ext_iff
instance : ToString NPrime where toString s := s!"{s.val}"
instance : Dvd NPrime where dvd a b := a.val ∣ b.val

-- interestingly, the following seems to shadow normal Nat ∈ Set Nat operations.
-- instance : Membership NPrime (Set Nat) where mem n s := n.val ∈ s
