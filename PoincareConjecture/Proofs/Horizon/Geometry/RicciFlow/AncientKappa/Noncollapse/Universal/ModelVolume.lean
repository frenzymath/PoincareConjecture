import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Model
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) RoundCylinderSpace :=
  RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)

local instance : IsManifold (𝓡 3) ∞ RoundCylinderSpace :=
  RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)

theorem roundCylinderMetric_complete : MetricComplete roundCylinderMetric := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 1))) RoundCylinderSpace :=
    RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let : IsManifold (𝓡 (2 + 1)) ∞ RoundCylinderSpace :=
    RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let h := rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
    2 (by norm_num)
  apply h.metricComplete_of_product_pullback roundCylinderMetric
    roundCylinderModelDiffeomorph
  · intro z v w
    rw [roundCylinderMetric_inner]
    change EvolvingRoundCylinderMetric 0 z v w =
      (rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
        2 (by norm_num)).inner z.1 v.1 w.1 + v.2 * w.2
    rw [rescaledMetric_inner,
      Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner]
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one,
      RiemannianMetric.euclideanMetric_inner]
  · dsimp only [MetricComplete]
    infer_instance

def universalNoncollapseModelPoint : RoundCylinderSpace :=
  (Classical.choice (show Nonempty UnitTwoSphere from by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 3))
      (x := 0) (r := 1)).mpr zero_le_one
    exact ⟨⟨x, hx⟩⟩), 0)

def universalNoncollapseModelVolume : ℝ :=
  (roundCylinderMetric.volumeMeasure
    (roundCylinderMetric.ball universalNoncollapseModelPoint (1 / 4))).toReal

theorem universalNoncollapseModelVolume_pos : 0 < universalNoncollapseModelVolume := by
  apply ENNReal.toReal_pos
  · exact (roundCylinderMetric.volumeMeasure_ball_pos universalNoncollapseModelPoint
      (by norm_num : (0 : ℝ) < 1 / 4)).ne'
  · exact (roundCylinderMetric.volumeMeasure_ball_lt_top roundCylinderMetric_complete
      universalNoncollapseModelPoint (1 / 4)).ne

end PoincareConjecture
