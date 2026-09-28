import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedMetricComparison
import PoincareConjecture.Proofs.M30.Thm11_8.LocalEmbeddingVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

theorem generalized_limit_ball_volume_lower_bound
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (N : ℕ) (hNt : ∀ k : ℕ, t ∈ Icc (-G.exhaustion.time (k + N)) 0)
    (p : G.limit.carrier.carrier) {r : ℝ} (hr : 0 < r) (kappa : ℝ)
    (hvolume : ∀ rho : ℝ, 0 < rho → rho < r → ∀ᶠ k in atTop,
      let h := normalizedBlowupSliceMetric S (G.subsequence (k + N)) t
      let e := generalizedSliceHomeomorph G (k + N) t (hNt k)
      ENNReal.ofReal (kappa * rho ^ 3) ≤ calibratedMetricVolume h (h.ball (e p) rho)) :
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (G.limit.flow.metric t) ((G.limit.flow.metric t).ball p r) := by
  let g := G.limit.flow.metric t
  let h (k : ℕ) := normalizedBlowupSliceMetric S (G.subsequence (k + N)) t
  let e (k : ℕ) := generalizedSliceHomeomorph G (k + N) t (hNt k)
  have hcomplete : MetricComplete g := G.limit.complete t ht
  rw [calibratedMetricVolume_eq_volumeMeasure]
  apply RiemannianMetric.ball_volume_lower_bound_of_local_tangent_comparisons
    g h e hcomplete p hr kappa
  · intro k x hx
    exact (generalizedSliceHomeomorph_contMDiffAt G (k + N) t (hNt k) hx).of_le
      (by simp)
  · intro k y hy
    exact (generalizedSliceHomeomorph_symm_contMDiffAt G (k + N) t (hNt k) hy).of_le
      (by simp)
  · intro K hK C hC
    exact eventually_generalized_tangent_comparison G ht N hNt hK hC
  · intro rho hrho hrhor
    simpa only [calibratedMetricVolume_eq_volumeMeasure] using hvolume rho hrho hrhor

end PoincareConjecture.M30
