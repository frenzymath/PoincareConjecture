import PoincareLib.Geometry.Riemannian.Metric

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/MetricBallTopology.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Topology of the actual selected metric balls

The comparison balls in Morgan-Tian Theorem 13.2, p. 333, and
Lemma 13.4, pp. 333-334, use the selected metric and original topology.
The induced extended metric realizes both simultaneously.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.SurgeryVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]

/-- The literal selected metric ball is open in the manifold topology
(MT Theorem 13.2, p. 333; Lemma 13.4, pp. 333-334). -/
theorem isOpen_metric_ball (g : RiemannianMetric n M) (p : M) (r : ℝ) :
    IsOpen (g.ball p r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have he : g.ball p r = Metric.eball p (ENNReal.ofReal r) := by
    ext y
    change edist p y < ENNReal.ofReal r ↔ edist y p < ENNReal.ofReal r
    rw [edist_comm]
  rw [he]
  exact Metric.isOpen_eball

/-- Closing a smaller ball stays inside a strictly larger one for the
actual selected metric (MT Lemma 13.4, pp. 333-334). -/
theorem closure_metric_ball_subset_ball (g : RiemannianMetric n M) (p : M)
    {r R : ℝ} (hR : 0 < R) (hrR : r < R) :
    closure (g.ball p r) ⊆ g.ball p R := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hc : IsClosed {y : M | g.edist p y ≤ ENNReal.ofReal r} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hs : closure (g.ball p r) ⊆ {y : M | g.edist p y ≤ ENNReal.ofReal r} := by
    apply closure_minimal _ hc
    intro y hy
    exact (show g.edist p y < ENNReal.ofReal r from hy).le
  intro y hy
  exact (hs hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR)

end PoincareMT.SurgeryVolume
