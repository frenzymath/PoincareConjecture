import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Distance

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set Filter MeasureTheory

namespace PoincareConjecture.EpsilonNeck

local instance : ChartedSpace RoundCylinderCoordinates RoundCylinderSpace :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ

private theorem roundCylinder_model_metric_pullback :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    let e := roundCylinderModelDiffeomorph
    ∀ (z : RoundCylinderSpace)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      roundCylinderMetric.inner (e z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
        (rescaledMetric
          (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2) 2
          (by norm_num)).inner z.1 v.1 w.1 + v.2 * w.2 := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  dsimp only
  intro z v w
  rw [roundCylinderMetric_inner]
  unfold EvolvingRoundCylinderMetric
  rw [rescaledMetric_inner]
  rw [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner]
  simp only [RiemannianMetric.euclideanMetric_inner]
  ring

private theorem roundCylinder_spherical_edist_le_pi (x y : UnitTwoSphere) :
    (rescaledMetric
      (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2) 2
      (by norm_num)).edist x y ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi) := by
  rw [rescaledMetric_edist]
  rw [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_edist_eq_angle
    (by norm_num : 1 ≤ 2)]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  apply ENNReal.ofReal_le_ofReal
  have hangle := Real.arccos_le_pi (1 - dist x y ^ 2 / 2)
  nlinarith [Real.pi_pos, Real.sqrt_nonneg 2]

theorem roundCylinder_edist_le :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ (z w : RoundCylinderSpace),
      roundCylinderMetric.edist z w ≤
        ENNReal.ofReal (Real.sqrt 2 * Real.pi + |z.2 - w.2|) := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  intro z w
  have hprod := RiemannianMetric.product_edist_bounds_of_pullback
    (rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2) 2
      (by norm_num)) roundCylinderMetric roundCylinderModelDiffeomorph
    (by exact roundCylinder_model_metric_pullback) z w
  have hs := roundCylinder_spherical_edist_le_pi z.1 w.1
  have hv : EDist.edist z.2 w.2 = ENNReal.ofReal |z.2 - w.2| := by
    rw [edist_dist, Real.dist_eq]
  rw [hv] at hprod
  have h := hprod.2.trans
    (add_le_add hs (le_rfl : ENNReal.ofReal |z.2 - w.2| ≤ _))
  rw [← ENNReal.ofReal_add (by positivity) (abs_nonneg _)] at h
  exact h

end PoincareConjecture.EpsilonNeck
