import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Model
import PoincareLib.Geometry.Riemannian.Metric.Product.Distance
import PoincareLib.Geometry.Riemannian.Measure.Balls

/-!
# A fixed positive model volume for universal noncollapsing

The radius-one-quarter ball in the scalar-normalized round cylinder has
positive finite volume. Both the model and its chosen center are fixed before
any ancient solution is supplied.
Reference: Morgan--Tian, Proposition 9.58, pp. 220--221.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

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

/-- The source model's fixed small-ball volume, in real-valued units. -/
def universalNoncollapseModelVolume : ℝ :=
  (roundCylinderMetric.volumeMeasure
    (roundCylinderMetric.ball universalNoncollapseModelPoint (1 / 4))).toReal

theorem universalNoncollapseModelVolume_pos : 0 < universalNoncollapseModelVolume := by
  apply ENNReal.toReal_pos
  · exact (roundCylinderMetric.volumeMeasure_ball_pos universalNoncollapseModelPoint
      (by norm_num : (0 : ℝ) < 1 / 4)).ne'
  · exact (roundCylinderMetric.volumeMeasure_ball_lt_top roundCylinderMetric_complete
      universalNoncollapseModelPoint (1 / 4)).ne

end PoincareMT
