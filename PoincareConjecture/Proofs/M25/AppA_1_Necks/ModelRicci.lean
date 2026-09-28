import PoincareConjecture.Proofs.M25.AppA_1_Necks.ModelScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FlowExtension
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Calculus












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff

namespace PoincareConjecture



theorem m25_roundCylinderMetric_ricci_transverse :
    let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ (D : LeviCivitaData roundCylinderMetric) (z : RoundCylinderSpace)
      (v w : TangentSpace (𝓡 3) z),
      D.ricci z v w = (1 / 2 : ℝ) * (roundCylinderMetric.inner z v w -
        mvfderiv (𝓡 3) (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) z v *
        mvfderiv (𝓡 3) (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) z w) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  dsimp only
  intro D z v w
  let g2 := rescaledMetric (roundSphereMetric 2) 2 (by norm_num)
  have hmetric (p : UnitTwoSphere × ℝ)
      (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
      roundCylinderMetric.inner (roundCylinderModelDiffeomorph p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph p a)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph p b) =
        g2.inner p.1 a.1 b.1 + a.2 * b.2 := by
    rw [roundCylinderMetric_inner]
    change 2 * (1 - 0) * (roundSphereMetric 2).inner p.1 a.1 b.1 + a.2 * b.2 =
      2 * (roundSphereMetric 2).inner p.1 a.1 b.1 + a.2 * b.2
    ring
  obtain ⟨hu, hz⟩ := RiemannianMetric.product_height_hasUnitGradient_and_hasZeroHessian
    g2 roundCylinderMetric D roundCylinderModelDiffeomorph hmetric
  have h := D.ricci_eq_scalar_transverse_of_parallel_gradient
    D.normalization_curvatureTensorCalculus
    (contMDiff_snd.comp roundCylinderModelDiffeomorph.symm.contMDiff) hu hz z v w
  rwa [roundCylinderMetric_scalar_one] at h




theorem roundCylinderEuclideanModelConnection_ricci
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanModelConnection.ricci x v w = (1 / 2 : ℝ) *
      (roundCylinderEuclideanModelMetric.inner x v w -
        ((RiemannianMetric.lineModelEquiv 2).symm v).2 *
        ((RiemannianMetric.lineModelEquiv 2).symm w).2) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  obtain ⟨p, hp⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 3)))
    (r := (1 : ℝ))).mpr zero_le_one
  let q : UnitTwoSphere := ⟨p, hp⟩
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let r : RoundCylinderSpace → ℝ := Prod.snd ∘ roundCylinderModelDiffeomorph.symm
  have hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r :=
    contMDiff_snd.comp roundCylinderModelDiffeomorph.symm.contMDiff
  have hcomp : r ∘ m25_roundCylinderEuclideanParametrization q = fun y => (T y).2 := by
    funext y
    simp [r, m25_roundCylinderEuclideanParametrization, T]
  have hheight (a : EuclideanSpace ℝ (Fin 3)) :
      mvfderiv (𝓡 3) r (m25_roundCylinderEuclideanParametrization q x)
        (mfderiv (𝓡 3) (𝓡 3) (m25_roundCylinderEuclideanParametrization q) x a) = (T a).2 := by
    have hc := mfderiv_comp_apply x (hr.mdifferentiable (by simp) _)
      ((roundCylinderEuclideanParametrization_contMDiff q).mdifferentiable (by simp) _) a
    rw [hcomp, mfderiv_eq_fderiv, T.hasFDerivAt.snd.fderiv] at hc
    exact hc.symm
  have h := roundCylinderEuclideanModelConnection.ricci_eq_of_local_isometry
    roundCylinderMetric.leviCivitaData isOpen_univ
    (roundCylinderEuclideanParametrization_contMDiff q).contMDiffOn
    (fun y _ a b => roundCylinderEuclideanModelMetric_pullback q y a b)
    (mem_univ x) v w
  rw [m25_roundCylinderMetric_ricci_transverse,
    ← roundCylinderEuclideanModelMetric_pullback q] at h
  change _ = (1 / 2 : ℝ) * (_ - mvfderiv (𝓡 3) r _ _ * mvfderiv (𝓡 3) r _ _) at h
  rwa [hheight, hheight] at h



theorem roundCylinderEuclideanModelConnection_ricci_zero_basis (i j : Fin 3) :
    roundCylinderEuclideanModelConnection.ricci 0
      (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j) =
      if i = j ∧ i ≠ 2 then 1 else 0 := by
  rw [roundCylinderEuclideanModelConnection_ricci]
  change (1 / 2 : ℝ) * (roundCylinderEuclideanModelCoefficients 0
    (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j) - _) = _
  simp only [roundCylinderEuclideanModelCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply, map_zero,
    m25_lineModelEquiv_symm_roundCylinderEuclideanBasis, roundCylinderModelCoefficients_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left,
      PiLp.single_apply, Fin.ext_iff]



theorem roundCylinderEuclideanModelConnection_ricci_zero_self
    (v : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanModelConnection.ricci 0 v v =
      ‖((RiemannianMetric.lineModelEquiv 2).symm v).1‖ ^ 2 := by
  rw [roundCylinderEuclideanModelConnection_ricci]
  change (1 / 2 : ℝ) * (roundCylinderEuclideanModelCoefficients 0 v v - _) = _
  simp only [roundCylinderEuclideanModelCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply, map_zero, roundCylinderModelCoefficients_apply]
  norm_num [real_inner_self_eq_norm_sq]
  ring

end PoincareConjecture
