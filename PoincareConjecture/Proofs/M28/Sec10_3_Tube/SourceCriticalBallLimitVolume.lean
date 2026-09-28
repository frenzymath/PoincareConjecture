import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.LimitVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem exists_criticalBall_limit_volume_bound
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.measurableSpace
    letI := G.limitCarrier.borelSpace
    letI := G.limitCarrier.t3Space
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∃ V : ℝ, 0 < V ∧ G.limitMetric.volumeMeasure univ ≤ ENNReal.ofReal V := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t3Space
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  obtain ⟨V, hV, hbound⟩ := H.exists_tubeCritical_volume_bound T A1
  refine ⟨8 * V, mul_pos (by norm_num) hV, ?_⟩
  have hlimit := G.volumeMeasure_univ_le_of_source_bound (ENNReal.ofReal V)
    (fun k => hbound (phi k))
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
    ENNReal.ofReal_ofNat] using hlimit

end PoincareConjecture.M28.CounterexampleNeckFamily
