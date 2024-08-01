import Mathlib
import Mathlib.Data.Finset.Basic

-- https://x.com/LongFormMath/status/1811519361716486427
/-

For n ≥ 1, the set {1, ..., 2*n} can be
partitioned into pairs {a₁, b₁},...,{aₙ, bₙ}
such that for each 1 ≤ i ≤ n, a₁ + b₁ is a prime.


a short informal proof:
https://math.stackexchange.com/questions/6526/partitioning-sets-such-that-the-sum-of-2-elements-is-prime
-/


-- i don't know how to expres it yet, though.

-- abbrev NatL := List Nat

-- open Lean List

-- def N (m : Nat) {hpos: m≥1} : Finset { n:Nat | n≥1 ∧ n ≤ 2*m } :=
--   List.range (2 * m) |>.map (· + 1) |>.toFinset

-- #check List.toSSet

-- theorem prime_pairs (m:PNat) (N: { n:Nat | pos n ∧ n ≤ 2 * m })
--   : ∃ a b : NatL, (∀n∈N, n∈a ≠ n∈b) ∧
