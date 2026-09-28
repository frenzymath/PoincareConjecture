import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallScalarLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.UniformCompactScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 1200000 in





theorem exists_eventual_compact_normalized_raw_scalar_bound
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (_D0 : LeviCivitaData G.limitMetric) (K : Set G.limitCarrier.carrier),
      IsCompact K → ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
        |(H.normalizedSliceConnection (phi (G.subsequence k))).scalarCurvature
          (G.embedding k x).val.val| ≤ B := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 K hK
  let D (k : ℕ) : LeviCivitaData (H.tubeCriticalMetric T A1 (phi k)) :=
    Classical.choice (exists_leviCivitaData (H.tubeCriticalMetric T A1 (phi k)))
  obtain ⟨B, hB, htail⟩ := G.exists_eventual_compact_scalar_bound D D0 K hK
  refine ⟨B, hB, ?_⟩
  filter_upwards [htail] with k hk
  intro x hx
  rw [H.normalizedSlice_scalar_eq,
    ← H.tubeCritical_scalar_eq T A1 (phi (G.subsequence k)) (D (G.subsequence k))]
  exact hk x hx

end PoincareConjecture.M28.CounterexampleNeckFamily
