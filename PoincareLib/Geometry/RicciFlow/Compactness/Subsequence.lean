import PoincareLib.Geometry.RicciFlow.Compactness.Convergence
import PoincareLib.Topology.Sequences.Diagonal

/-!
# Subsequences of pointed Ricci flows

All frozen compactness hypotheses survive passage to a strictly increasing
subsequence. A geometric limit of that subsequence is a geometric limit of
the original sequence, with exactly the same limit flow and exhaustion.
-/

set_option autoImplicit false

namespace PoincareMT

namespace PointedFlowSequence

/-- Reindex a sequence without changing any of its pointed flows. -/
def subsequence {n : ℕ} {T' T : ℝ} (S : PointedFlowSequence n T' T)
    (φ : ℕ → ℕ) : PointedFlowSequence n T' T where
  carrier k := S.carrier (φ k)
  flow k := S.flow (φ k)

end PointedFlowSequence

namespace PointedRicciFlowCompactnessHypotheses

/-- The eventual compactness, curvature, and volume hypotheses are preserved
by a strictly increasing reindexing. -/
def subsequence {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    PointedRicciFlowCompactnessHypotheses n T' T where
  time_bounds := H.time_bounds
  sequence := H.sequence.subsequence φ
  volume_compatibility k := H.volume_compatibility (φ k)
  zero_time_ball_compact A hA := hφ.tendsto_atTop.eventually (H.zero_time_ball_compact A hA)
  spacetime_control A hA I hI hIc hI0 hIt := by
    obtain ⟨K, hK, he⟩ := H.spacetime_control A hA I hI hIc hI0 hIt
    exact ⟨K, hK, hφ.tendsto_atTop.eventually he⟩
  all_time_curvature_control A hA := by
    obtain ⟨K, hK, hbound⟩ := H.all_time_curvature_control A hA
    exact ⟨K, hK, hφ.tendsto_atTop.eventually hbound⟩
  noncollapsing := by
    obtain ⟨r, κ, hr, hκ, hvolume⟩ := H.noncollapsing
    exact ⟨r, κ, hr, hκ, hφ.tendsto_atTop.eventually hvolume⟩

end PointedRicciFlowCompactnessHypotheses

namespace PointedGeometricConvergence

/-- Compose subsequences while preserving all convergence and embedding data. -/
def ofSubsequence {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (L : PointedGeometricConvergence (S.subsequence φ)) :
    PointedGeometricConvergence S where
  limitCarrier := L.limitCarrier
  limitFlow := L.limitFlow
  subsequence := φ ∘ L.subsequence
  subsequence_strictMono := hφ.comp L.subsequence_strictMono
  exhaustion := L.exhaustion
  exhaustion_open := L.exhaustion_open
  exhaustion_connected := L.exhaustion_connected
  exhaustion_compactClosure := L.exhaustion_compactClosure
  exhaustion_increasing := L.exhaustion_increasing
  exhaustion_covers := L.exhaustion_covers
  embedding := L.embedding
  base_in_exhaustion := L.base_in_exhaustion
  base_preserving := L.base_preserving
  pullback_metric_converges := L.pullback_metric_converges
  pullback_metric_CInfinity := L.pullback_metric_CInfinity

end PointedGeometricConvergence

/-- Completeness is unchanged when a subsequential limit is regarded as a
limit of the original sequence. -/
def PointedRicciFlowCompactnessConclusion.ofSubsequence
    {n : ℕ} {T' T : ℝ} {H : PointedRicciFlowCompactnessHypotheses n T' T}
    {φ : ℕ → ℕ} {hφ : StrictMono φ}
    (L : PointedRicciFlowCompactnessConclusion (H.subsequence φ hφ)) :
    PointedRicciFlowCompactnessConclusion H where
  geometric_limit := L.geometric_limit.ofSubsequence hφ
  complete_interior := L.complete_interior

end PoincareMT
