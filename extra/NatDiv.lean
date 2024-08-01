-- some theorems about division in Nat
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.ModEq

variable {m n d k: Nat}  {hdpos: 0 < d}

theorem nat_le_mul_div_succ  {hdpos: 0 < d}: n ≤ d * (n/d + 1) := by
  simp[Nat.mul_add]
  conv => left; rw[← Nat.div_add_mod n d]
  have := Nat.mod_lt n hdpos
  omega

@[simp] theorem nat_div_mod (d n:Nat): d*(n/d) = (n-n%d):= by
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

theorem mod_lt_of_lt_div_eq : m<n → (m/d = n/d) → (m%d < n%d) := by
  intro hmn hdiv
  rwa[←m.div_add_mod d, ←n.div_add_mod d, hdiv, Nat.add_lt_add_iff_left] at hmn

theorem div_lt_of_lt_mod_eq : m<n → (m%d = n%d) → (m/d < n/d) := by
  intro hmn hmod
  rw[←m.div_add_mod d, ←n.div_add_mod d, hmod, Nat.add_lt_add_iff_right] at hmn
  exact (Nat.mul_lt_mul_left hdpos).mp hmn
