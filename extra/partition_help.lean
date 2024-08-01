-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20How.20to.20simplify.20.28List.2Emap.20f.20List.2Erange.20n.29.3F

import Mathlib.Tactic


def partition (ks:List Nat) (d j: Nat) (hks: 0 < ks.length): List Nat :=
  List.range (j*ks.length) |>.map λi =>
    ks[i%ks.length]'(List.mod_length ks i hks) + (i/ks.length) * d

theorem length_partition (ks:List Nat) (d j: Nat) (hks: 0 < ks.length)
  : (partition ks d j hks).length = j * ks.length
  := by simp[partition]

theorem partition_k (ks:List Nat) (d j: Nat) (hks: 0 < ks.length) (i) (h)
  : (partition ks d j hks)[i] =
    ks[i%ks.length]'(List.mod_length ks i hks) + (i/ks.length) * d
  := by simp[partition]
