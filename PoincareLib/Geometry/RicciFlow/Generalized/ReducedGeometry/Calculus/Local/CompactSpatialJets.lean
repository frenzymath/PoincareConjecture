import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Coordinates.ClosedChartCoefficients
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartCoercivity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform spatial coefficient bounds on a closed time product

The local coordinate comparison for Morgan-Tian Corollary 6.79,
pp. 144-145. Compactness bounds actual spatial within derivatives;
the convex mean-value estimate gives constants uniform in the
retained closed time interval, including physical time endpoints.
-/

set_option autoImplicit false
-- Spatial derivatives of quadratic coefficients use nested operator spaces.
set_option synthInstance.maxSize 2048

open Set
open scoped ContDiff NNReal

namespace PoincareMT.M14

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth closed-time coefficients are uniformly Lipschitz in space
on a compact convex spatial set, the coefficient bound in the local
comparison for Corollary 6.79, pp. 144-145. -/
theorem compact_spatial_lipschitz_within {a b : ℝ} (hab : a < b)
    {U S : Set E} (hU : IsOpen U) (hS : IsCompact S) (hconvex : Convex ℝ S) (hsub : S ⊆ U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) :
    ∃ K : ℝ≥0, ∀ s ∈ Icc a b, LipschitzOnWith K (fun z => f (s, z)) S := by
  let D := M08.spatialWithinFDeriv (Icc a b) U f
  have hD := M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hU f hf
  have hsmall : Icc a b ×ˢ S ⊆ Icc a b ×ˢ U := prod_mono_right hsub
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn
    (hD.continuousOn.mono hsmall)
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro s hs
  apply hconvex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz => (M08.hasFDerivAt_spatialWithin hU f hf hs (hsub hz)).hasFDerivWithinAt)
  intro z hz
  change ‖D (s, z)‖ ≤ max C 0
  exact (hC (s, z) ⟨hs, hz⟩).trans (le_max_left _ _)

end PoincareMT.M14
