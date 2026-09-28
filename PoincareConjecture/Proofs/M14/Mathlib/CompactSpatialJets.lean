import PoincareConjecture.Proofs.M08.ClosedChartCoefficients
import PoincareConjecture.Proofs.M08.ChartCoercivity
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false

set_option synthInstance.maxSize 2048

open Set
open scoped ContDiff NNReal

namespace PoincareConjecture.M14

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




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

end PoincareConjecture.M14
