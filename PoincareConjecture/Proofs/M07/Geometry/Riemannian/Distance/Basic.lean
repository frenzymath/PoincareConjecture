import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Completeness

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]

theorem edist_ne_top (g : RiemannianMetric n M) (x y : M) :
    g.edist x y ≠ ⊤ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact Poincare.edist_ne_top_of_preconnected x y

theorem toReal_edist_triangle (g : RiemannianMetric n M) (x y z : M) :
    (g.edist x z).toReal ≤ (g.edist x y).toReal + (g.edist y z).toReal := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← ENNReal.toReal_add (g.edist_ne_top x y) (g.edist_ne_top y z)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨g.edist_ne_top x y, g.edist_ne_top y z⟩) Manifold.riemannianEDist_triangle

theorem abs_toReal_edist_sub_le (g : RiemannianMetric n M) (O x y : M) :
    |(g.edist O x).toReal - (g.edist O y).toReal| ≤ (g.edist x y).toReal := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hxy := g.toReal_edist_triangle O x y
  have hyx := g.toReal_edist_triangle O y x
  have hcomm : g.edist y x = g.edist x y := Manifold.riemannianEDist_comm
  rw [hcomm] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem continuous_toReal_edist (g : RiemannianMetric n M) (O : M) :
    Continuous (fun x ↦ (g.edist O x).toReal) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (ENNReal.continuousAt_toReal (g.edist_ne_top O x)).comp
    (continuous_const.edist continuous_id).continuousAt

end PoincareConjecture.RiemannianMetric
