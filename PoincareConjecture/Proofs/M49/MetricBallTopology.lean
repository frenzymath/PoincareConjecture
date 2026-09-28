import PoincareConjecture.Definitions.Ch01.RiemannianMetric









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M49

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]



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

end PoincareConjecture.M49
