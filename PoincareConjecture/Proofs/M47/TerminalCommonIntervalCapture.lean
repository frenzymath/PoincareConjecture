import PoincareConjecture.Proofs.M47.LimitNoncollapseCapture
import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem terminalCommonInterval_closure_ball_subset
    (g : RiemannianMetric 3 M) (p : M) (R : ℝ) :
    closure (g.ball p R) ⊆ {z | g.edist p z ≤ ENNReal.ofReal R} := by
  let : EMetricSpace M := g.toEMetricSpace
  have hclosed : IsClosed {z | g.edist p z ≤ ENNReal.ofReal R} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  apply closure_minimal ?_ hclosed
  intro z hz
  exact (show g.edist p z < ENNReal.ofReal R from hz).le

theorem terminalCommonInterval_compact_ball_closure
    (g : RiemannianMetric 3 M) (hg : MetricComplete g) (p : M) (R : ℝ) :
    IsCompact (closure (g.ball p R)) :=
  (g.isCompact_closedBall_of_metricComplete hg p R).of_isClosed_subset
    isClosed_closure (terminalCommonInterval_closure_ball_subset g p R)

variable {N : Type v} [TopologicalSpace N] [T2Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

theorem terminalCommonInterval_capture_of_closed_buffer
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (hg : MetricComplete g) (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target)
    (p : M) {R r C : ℝ} (hR : 0 < R) (hC : 0 < C) (hCr : C * r < R)
    (hsource : {z | g.edist p z ≤ ENNReal.ofReal R} ⊆ e.source)
    (hbound : ∀ z, g.edist p z ≤ ENNReal.ofReal R →
      ∀ v : TangentSpace (𝓡 3) z,
        g.tangentNorm z v ≤ C * h.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v)) :
    h.ball (e p) r ⊆ e '' g.ball p (C * r) := by
  have hclosed := terminalCommonInterval_closure_ball_subset g p R
  apply limitNoncollapse_capture_ball g h e p hR hC hCr
    (terminalCommonInterval_compact_ball_closure g hg p R) (hclosed.trans hsource)
    (fun y hy => (hi y hy).contMDiffAt (e.open_target.mem_nhds hy))
  rintro _ ⟨z, hz, rfl⟩ v
  have hzs : z ∈ e.source := hsource (hclosed hz)
  apply g.inverse_tangentNorm_le_of_forward_lower_bound h e hf hi (e.map_source hzs)
  intro w
  rw [e.left_inv hzs]
  exact hbound z (hclosed hz) w

end PoincareConjecture.M47
