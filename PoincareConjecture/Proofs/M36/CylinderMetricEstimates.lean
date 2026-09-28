import PoincareConjecture.Proofs.M36.CylinderDualBounds
import PoincareConjecture.Proofs.M36.CurvatureTrace
import PoincareConjecture.Definitions.Ch04.Pinching
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem cylinderHeightCovector_mvfderiv (x v : E₃) :
    mvfderiv (𝓡 3) cylinderHeightCovector x v = cylinderHeightCovector v := by
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, cylinderHeightCovector.fderiv,
    NormedSpace.fromTangentSpace]
  rfl

theorem cylinderMetric_gradient_error
    (g : RiemannianMetric 3 E₃) (D : LeviCivitaData g) {rho : ℝ}
    (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 2)
    (hA : ‖g.euclideanCoefficients 0 - cylinderModelField 0‖ ≤ rho) :
    |g.inner 0 (D.gradient cylinderHeightCovector 0) (D.gradient cylinderHeightCovector 0) - 1| ≤
      2 * rho := by
  apply (cylinder_close_dual_height (g.euclideanCoefficients 0) hrho hsmall hA
    (D.gradient cylinderHeightCovector 0) ?_).2
  intro v
  exact (D.inner_gradient cylinderHeightCovector 0 v).trans (cylinderHeightCovector_mvfderiv 0 v)

theorem cylinderMetric_sectional_bounds
    (g : RiemannianMetric 3 E₃) (D : LeviCivitaData g) {rho tau : ℝ}
    (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 2) (htau : 0 ≤ tau)
    (hA : ‖g.euclideanCoefficients 0 - cylinderModelField 0‖ ≤ rho)
    (hT : ∀ a : Fin 4 → Fin 3,
      |D.curvatureTensor 0 (EuclideanSpace.basisFun (Fin 3) ℝ (a 0))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 1))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 2))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 3)) -
        cylinderModelCurvature (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j))| ≤ tau)
    (v w : E₃) (hvw : LeviCivitaData.IsOrthonormalPair g 0 v w) :
    -324 * tau ≤ D.sectionalCurvature 0 v w ∧
      |D.sectionalCurvature 0 v w -
        (1 - cylinderHeightCovector v ^ 2 - cylinderHeightCovector w ^ 2) / 2| ≤
          324 * tau + 12 * rho := by
  obtain ⟨T, hreal⟩ := D.exists_multilinear_curvatureTensor 0
  have hcomp (a : Fin 4 → Fin 3) :
      |(T - cylinderModelCurvature)
        (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j))| ≤ tau := by
    rw [sub_apply, ← hreal]
    exact hT a
  have h := cylinder_close_plane_bounds (g.euclideanCoefficients 0) T
    hrho hsmall htau hA hcomp v w hvw.1 hvw.2.1 hvw.2.2
  rw [← hreal] at h
  have hsec : D.sectionalCurvature 0 v w = D.curvatureTensor 0 v w v w := by
    simp [LeviCivitaData.sectionalCurvature, hvw.1, hvw.2.1, hvw.2.2]
  change -324 * tau ≤ D.curvatureTensor 0 v w v w ∧
    |D.curvatureTensor 0 v w v w -
      (1 - cylinderHeightCovector v ^ 2 - cylinderHeightCovector w ^ 2) / 2| ≤
        324 * tau + 12 * rho at h
  rwa [hsec]

theorem cylinderMetric_scalar_error
    (g : RiemannianMetric 3 E₃) (D : LeviCivitaData g) {rho tau : ℝ}
    (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 2) (htau : 0 ≤ tau)
    (hA : ‖g.euclideanCoefficients 0 - cylinderModelField 0‖ ≤ rho)
    (hT : ∀ a : Fin 4 → Fin 3,
      |D.curvatureTensor 0 (EuclideanSpace.basisFun (Fin 3) ℝ (a 0))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 1))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 2))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 3)) -
        cylinderModelCurvature (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j))| ≤ tau) :
    |D.scalarCurvature 0 - 1| ≤ 1944 * tau + 76 * rho := by
  classical
  let U := D.gradient cylinderHeightCovector 0
  let G := g.inner 0 U U
  have hG : |G - 1| ≤ 2 * rho := cylinderMetric_gradient_error g D hrho hsmall hA
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E₃ → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (0 : E₃)) = 3 := by
    change Module.finrank ℝ E₃ = 3
    simp
  let b := (g.orthonormalBasis 0).reindex (finCongr hdim)
  have hgrad : (∑ i : Fin 3, cylinderHeightCovector (b i) ^ 2) = G := by
    have hdual (i : Fin 3) : cylinderHeightCovector (b i) = g.inner 0 U (b i) := by
      rw [← cylinderHeightCovector_mvfderiv 0 (b i)]
      exact (D.inner_gradient cylinderHeightCovector 0 (b i)).symm
    simp_rw [hdual]
    exact (b.sum_sq_inner_left U).trans (real_inner_self_eq_norm_sq U).symm
  have hp (i j : Fin 3) (hij : i ≠ j) :
      |D.sectionalCurvature 0 (b i) (b j) -
        (1 - cylinderHeightCovector (b i) ^ 2 - cylinderHeightCovector (b j) ^ 2) / 2| ≤
          324 * tau + 12 * rho :=
    (cylinderMetric_sectional_bounds g D hrho hsmall htau hA hT (b i) (b j)
      ⟨b.inner_eq_one i, b.inner_eq_one j, b.inner_eq_zero hij⟩).2
  have htrace : |D.scalarCurvature 0 - (3 - 2 * G)| ≤ 6 * (324 * tau + 12 * rho) := by
    obtain ⟨h01L, h01U⟩ := abs_le.mp (hp 0 1 (by decide))
    obtain ⟨h02L, h02U⟩ := abs_le.mp (hp 0 2 (by decide))
    obtain ⟨h10L, h10U⟩ := abs_le.mp (hp 1 0 (by decide))
    obtain ⟨h12L, h12U⟩ := abs_le.mp (hp 1 2 (by decide))
    obtain ⟨h20L, h20U⟩ := abs_le.mp (hp 2 0 (by decide))
    obtain ⟨h21L, h21U⟩ := abs_le.mp (hp 2 1 (by decide))
    rw [scalarCurvature_eq_sum_sectional D 0 b]
    simp only [Fin.sum_univ_three, sectionalCurvature_self] at hgrad ⊢
    apply abs_le.mpr
    constructor <;> linarith only [h01L, h01U, h02L, h02U, h10L, h10U,
      h12L, h12U, h20L, h20U, h21L, h21U, hgrad]
  have hmodel : |3 - 2 * G - 1| ≤ 4 * rho := by
    obtain ⟨hL, hU⟩ := abs_le.mp hG
    apply abs_le.mpr
    constructor <;> linarith only [hL, hU]
  calc
    _ ≤ |D.scalarCurvature 0 - (3 - 2 * G)| + |3 - 2 * G - 1| := abs_sub_le _ _ _
    _ ≤ 6 * (324 * tau + 12 * rho) + 4 * rho := add_le_add htrace hmodel
    _ = _ := by ring

theorem cylinderMetric_height_hessian_bound
    (g : RiemannianMetric 3 E₃) (D : LeviCivitaData g) {rho sigma : ℝ}
    (hsmall : rho ≤ 1 / 2)
    (hA : ‖g.euclideanCoefficients 0 - cylinderModelField 0‖ ≤ rho)
    (hfirst : ‖fderiv ℝ g.euclideanCoefficients 0‖ ≤ sigma) (v w : E₃) :
    |D.hessian cylinderHeightCovector 0 v w| ≤
      6 * sigma * g.tangentNorm 0 v * g.tangentNorm 0 w := by
  have hd : ‖fderiv ℝ cylinderHeightCovector 0‖ ≤ 1 := by
    rw [cylinderHeightCovector.fderiv]
    exact cylinderHeightCovector_norm_le_one
  have hdd : ‖fderiv ℝ (fderiv ℝ cylinderHeightCovector) 0‖ ≤ 0 := by
    have hconst : fderiv ℝ cylinderHeightCovector = fun _ => cylinderHeightCovector :=
      funext fun _ => cylinderHeightCovector.fderiv
    rw [hconst, fderiv_const_apply, norm_zero]
  have h := D.abs_hessian_le_of_elliptic_coordinate_bounds
    cylinderHeightCovector.contDiff.contDiffAt (by norm_num : (0 : ℝ) < 1 / 2)
    (cylinder_close_bilinear_lower (g.euclideanCoefficients 0) hsmall hA)
    hd hdd hfirst v w
  convert h using 1
  ring

end PoincareConjecture.M36
