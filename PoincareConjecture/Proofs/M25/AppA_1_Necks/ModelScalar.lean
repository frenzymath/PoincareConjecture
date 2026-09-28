import PoincareConjecture.Proofs.M25.AppA_1_Necks.ModelMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff

namespace PoincareConjecture

theorem roundCylinderMetric_scalar_one :
    let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ (D : LeviCivitaData roundCylinderMetric) (z : RoundCylinderSpace),
      D.scalarCurvature z = 1 := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  dsimp only
  intro D z
  let gS := roundSphereMetric 2
  let DS := gS.leviCivitaData
  let g2 := rescaledMetric gS 2 (by norm_num)
  let D2 := rescaledMetric_connection gS DS 2 (by norm_num)
  have hS : DS.scalarCurvature z.1 = 2 := by
    have h := DS.scalarCurvature_of_constant_sectional z.1 1
      (fun u v huv => roundSphereMetric_sectionalCurvature DS z.1 u v huv)
    norm_num at h ⊢
    exact h
  have h2 : D2.scalarCurvature z.1 = 1 := by
    rw [rescaledMetric_scalarCurvature, hS]
    norm_num
  have hmetric (p : UnitTwoSphere × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
      roundCylinderMetric.inner (roundCylinderModelDiffeomorph p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph p w) =
        g2.inner p.1 v.1 w.1 + v.2 * w.2 := by
    rw [roundCylinderMetric_inner]
    change 2 * (1 - 0) * gS.inner p.1 v.1 w.1 + v.2 * w.2 =
      2 * gS.inner p.1 v.1 w.1 + v.2 * w.2
    ring
  exact (RiemannianMetric.scalarCurvature_eq_of_line_product g2
    roundCylinderMetric D2 D roundCylinderModelDiffeomorph hmetric z).trans h2

noncomputable def m25_roundCylinderEuclideanParametrization (q : UnitTwoSphere)
    (x : EuclideanSpace ℝ (Fin 3)) : RoundCylinderSpace :=
  roundCylinderModelDiffeomorph
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      ((RiemannianMetric.lineModelEquiv 2).symm x).1,
      ((RiemannianMetric.lineModelEquiv 2).symm x).2)

theorem roundCylinderEuclideanParametrization_contMDiff (q : UnitTwoSphere) :
    let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    ContMDiff (𝓡 3) (𝓡 3) ∞ (m25_roundCylinderEuclideanParametrization q) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  exact roundCylinderModelDiffeomorph.contMDiff.comp
    ((cylinderChart_symm_smooth q).comp
      (RiemannianMetric.lineModelEquiv 2).symm.contDiff.contMDiff)

theorem roundCylinderEuclideanModelMetric_pullback (q : UnitTwoSphere) :
    let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ (x v w : EuclideanSpace ℝ (Fin 3)),
      roundCylinderEuclideanModelMetric.inner x v w =
        roundCylinderMetric.inner (m25_roundCylinderEuclideanParametrization q x)
          (mfderiv (𝓡 3) (𝓡 3) (m25_roundCylinderEuclideanParametrization q) x v)
          (mfderiv (𝓡 3) (𝓡 3) (m25_roundCylinderEuclideanParametrization q) x w) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  dsimp only
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let f := fun y : RoundCylinderCoordinates => roundCylinderModelDiffeomorph
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)
  have hround : (fun z v w => 1 * roundCylinderPullback roundCylinderMetric
      roundCylinderModelDiffeomorph z v w) = EvolvingRoundCylinderMetric 0 := by
    funext z v w
    rw [one_mul]
    exact roundCylinderMetric_inner z v w
  have hcoef (y : RoundCylinderCoordinates) :
      roundCylinderMetric.parametrizedCoefficients f y = roundCylinderModelCoefficients y := by
    simpa only [one_smul] using parametrizedCoefficients_cylinder_of_normalized_pullback
      roundCylinderMetric roundCylinderModelDiffeomorph.contMDiff 1 hround q y
  have hparam := RiemannianMetric.parametrizedCoefficients_comp_parameterEquiv
    roundCylinderMetric T f
  intro x v w
  have hx := congrArg (fun A => A x v w) hparam
  dsimp only at hx
  rw [hcoef] at hx
  exact hx.symm

theorem roundCylinderEuclideanModelConnection_scalar_one
    (x : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanModelConnection.scalarCurvature x = 1 := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  obtain ⟨p, hp⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 3)))
    (r := (1 : ℝ))).mpr zero_le_one
  let q : UnitTwoSphere := ⟨p, hp⟩
  have h := roundCylinderEuclideanModelConnection.scalarCurvature_eq_of_local_isometry
    roundCylinderMetric.leviCivitaData isOpen_univ
    (roundCylinderEuclideanParametrization_contMDiff q).contMDiffOn
    (fun y _ v w => roundCylinderEuclideanModelMetric_pullback q y v w)
    (mem_univ x)
  exact h.trans (roundCylinderMetric_scalar_one _ _)

end PoincareConjecture
