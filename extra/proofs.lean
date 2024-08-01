import MathLib.Data.List.Sort

lemma sorted_indices (xs:List Nat) {hsort: List.Sorted (·<·) xs} (i j:Nat) (hij: i<j) (hj: j<xs.length)
  : (xs[i]'(by omega) < xs[j]'hj) := by
  conv at hsort => dsimp[List.Sorted]; rw[List.pairwise_iff_get]
  simp_all
