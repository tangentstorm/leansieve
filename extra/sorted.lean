import MathLib.Data.List.Sort

theorem sorted_get' (xs:List Nat) {hsort: List.Sorted (·<·) xs} (i j:Fin xs.length) (hij: i<j)
  : (xs[i] < xs[j]) := by
  conv at hsort => dsimp[List.Sorted]; rw[List.pairwise_iff_get]
  simp_all


theorem sorted_get (xs:List Nat) {hsort: List.Sorted (·<·) xs} (i j:Nat) (hij: i<j) (hj: j<xs.length)
  : (xs[i]'(by omega) < xs[j]'hj) := by
  sorry
  -- have := sorted_get' xs i j hij

  -- aesop
