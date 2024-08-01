-- victor's a guy that sometimes asks questions on the new members channel
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.NormedSpace.Basic

open Set Function Topology Metric ContinuousLinearMap Filter Units

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable [Nontrivial X] [Nontrivial Y]
-- Define the open subset Ω of X
variable (Ω : Set X) (hΩ : IsOpen Ω)
-- Define the point x₀ in Ω
variable (x₀ : X) (hx₀ : x₀ ∈ Ω)
-- Define the C¹ mapping f: Ω → Y
variable (f : X → Y) (hf : ContDiffOn ℝ 1 f Ω)
-- Define the radius r
variable (r : ℝ) (hr : 0 < r)
-- Define f' as a mapping
variable (f' : X → X ≃L[ℝ] Y)
         (hf' : ∀ x ∈ Ω, HasFDerivAt f (f' x : X →L[ℝ] Y) x)

-- Auxiliary function h
noncomputable def h (x : X) : X := (f' x₀).symm (f x)
noncomputable def h' (x : X) : X ≃L[ℝ] X := (f' x).trans (f' x₀).symm
variable (hh' : ∀ x ∈ Ω, HasFDerivAt (h x₀ f f') (h' x₀ f' x : X →L[ℝ] X) x)


lemma h'x₀_eq_id : h' x₀ f' x₀ = ContinuousLinearMap.id ℝ X := by
  unfold h'
  ext x₀.symm_apply_apply
  aesop
