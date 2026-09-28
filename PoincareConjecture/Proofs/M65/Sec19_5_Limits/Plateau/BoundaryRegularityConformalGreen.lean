import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Boundary

open M65StrictTrace

theorem diskBoundaryCoordinate_columns (p : ℂ) (z : LoopPlane) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    let P := diskBoundaryCoordinate p
    fderiv ℝ P z (e 0) = -(P z 1) • e 0 + (P z 0) • e 1 ∧
      fderiv ℝ P z (e 1) = -(P z 0) • e 0 - (P z 1) • e 1 := by
  let E := orthonormalBasisOneI.repr
  have hd := E.toContinuousLinearEquiv.hasFDerivAt.comp z
    (((hasDerivAt_boundaryCoordinate p (E.symm z)).hasFDerivAt.restrictScalars ℝ).comp z
      E.symm.toContinuousLinearEquiv.hasFDerivAt)
  dsimp only
  erw [hd.fderiv]
  constructor <;> ext i <;> fin_cases i <;>
    simp [E, diskBoundaryCoordinate, Complex.orthonormalBasisOneI_repr_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply, EuclideanSpace.basisFun_apply]

theorem diskBoundaryCoordinate_det {p : ℂ} (hp : ‖p‖ = 1) (z : LoopPlane) :
    (fderiv ℝ (diskBoundaryCoordinate p) z).det =
      Real.exp (-z 1) ^ 2 := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let P := diskBoundaryCoordinate p
  obtain ⟨h0, h1⟩ := diskBoundaryCoordinate_columns p z
  change LinearMap.det (fderiv ℝ P z).toLinearMap = _
  rw [← LinearMap.det_toMatrix e.toBasis, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis]
  change (fderiv ℝ P z (e 0)) 0 * (fderiv ℝ P z (e 1)) 1 -
    (fderiv ℝ P z (e 1)) 0 * (fderiv ℝ P z (e 0)) 1 = _
  rw [h0, h1]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  norm_num [e, EuclideanSpace.basisFun_apply]
  have hn : ‖P z‖ ^ 2 = (P z 0) ^ 2 + (P z 1) ^ 2 := by
    simpa only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using
      EuclideanSpace.norm_sq_eq (P z)
  rw [norm_diskBoundaryCoordinate hp] at hn
  nlinarith

private theorem boundary_coordinate_partial (p : ℂ) (z : LoopPlane) (i k : Fin 2) :
    fderiv ℝ (fun w => diskBoundaryCoordinate p w i) z
      (EuclideanSpace.basisFun (Fin 2) ℝ k) =
        (fderiv ℝ (diskBoundaryCoordinate p) z (EuclideanSpace.basisFun (Fin 2) ℝ k)) i := by
  have hd := (EuclideanSpace.proj i).hasFDerivAt.comp z
    ((contDiff_diskBoundaryCoordinate p).differentiable (by simp) z).hasFDerivAt
  exact congrArg (fun L => L (EuclideanSpace.basisFun (Fin 2) ℝ k)) hd.fderiv

theorem diskBoundaryCoordinate_cofactor_divergence (p : ℂ) (z : LoopPlane) (i : Fin 2) :
    (∑ k : Fin 2, fderiv ℝ (fun w =>
      (fderiv ℝ (diskBoundaryCoordinate p) w (EuclideanSpace.basisFun (Fin 2) ℝ k)) i)
        z (EuclideanSpace.basisFun (Fin 2) ℝ k)) = 0 := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let P := diskBoundaryCoordinate p
  have h00 : (fun w => (fderiv ℝ P w (e 0)) 0) = fun w => -P w 1 := by
    funext w
    rw [(diskBoundaryCoordinate_columns p w).1]
    simp [P, EuclideanSpace.basisFun_apply]
  have h01 : (fun w => (fderiv ℝ P w (e 1)) 0) = fun w => -P w 0 := by
    funext w
    rw [(diskBoundaryCoordinate_columns p w).2]
    simp [P, EuclideanSpace.basisFun_apply]
  have h10 : (fun w => (fderiv ℝ P w (e 0)) 1) = fun w => P w 0 := by
    funext w
    rw [(diskBoundaryCoordinate_columns p w).1]
    simp [P, EuclideanSpace.basisFun_apply]
  have h11 : (fun w => (fderiv ℝ P w (e 1)) 1) = fun w => -P w 1 := by
    funext w
    rw [(diskBoundaryCoordinate_columns p w).2]
    simp [P, EuclideanSpace.basisFun_apply]
  change (∑ k : Fin 2, fderiv ℝ (fun w => (fderiv ℝ P w (e k)) i) z (e k)) = 0
  fin_cases i
  · rw [Fin.sum_univ_two]
    change fderiv ℝ (fun w => (fderiv ℝ P w (e 0)) 0) z (e 0) +
      fderiv ℝ (fun w => (fderiv ℝ P w (e 1)) 0) z (e 1) = 0
    rw [h00, h01, fderiv_fun_neg, fderiv_fun_neg]
    simp only [neg_apply, boundary_coordinate_partial, P, e]
    rw [(diskBoundaryCoordinate_columns p z).1, (diskBoundaryCoordinate_columns p z).2]
    simp [EuclideanSpace.basisFun_apply]
  · rw [Fin.sum_univ_two]
    change fderiv ℝ (fun w => (fderiv ℝ P w (e 0)) 1) z (e 0) +
      fderiv ℝ (fun w => (fderiv ℝ P w (e 1)) 1) z (e 1) = 0
    rw [h10, h11, fderiv_fun_neg]
    simp only [neg_apply, boundary_coordinate_partial, P, e]
    rw [(diskBoundaryCoordinate_columns p z).1, (diskBoundaryCoordinate_columns p z).2]
    simp [EuclideanSpace.basisFun_apply]

theorem diskBoundaryCoordinate_test_divergence {p : ℂ} (hp : ‖p‖ = 1)
    (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (z : LoopPlane) (i : Fin 2) :
    (∑ k : Fin 2, fderiv ℝ (fun w =>
      test (diskBoundaryCoordinate p w) *
        (fderiv ℝ (diskBoundaryCoordinate p) w (EuclideanSpace.basisFun (Fin 2) ℝ k)) i)
          z (EuclideanSpace.basisFun (Fin 2) ℝ k)) =
      Real.exp (-z 1) ^ 2 *
        fderiv ℝ test (diskBoundaryCoordinate p z) (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let P := diskBoundaryCoordinate p
  let A := fderiv ℝ P z
  have hP := contDiff_diskBoundaryCoordinate p
  have hcoef (k : Fin 2) : DifferentiableAt ℝ (fun w => (fderiv ℝ P w (e k)) i) z :=
    (EuclideanSpace.proj i).differentiableAt.comp z
      (((hP.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiable (by simp) z).clm_apply
        (differentiableAt_const (e k)))
  have hprod (k : Fin 2) : fderiv ℝ (fun w => test (P w) * (fderiv ℝ P w (e k)) i) z (e k) =
      fderiv ℝ test (P z) (A (e k)) * (A (e k)) i +
        test (P z) * fderiv ℝ (fun w => (fderiv ℝ P w (e k)) i) z (e k) := by
    have htp := (ht.differentiable one_ne_zero (P z)).hasFDerivAt.comp z
      (hP.differentiable (by simp) z).hasFDerivAt
    have hd := htp.mul (hcoef k).hasFDerivAt
    dsimp only [Pi.mul_def, Function.comp_def] at hd
    simpa only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply, A, P,
      ContinuousLinearMap.comp_apply, mul_comm, add_comm] using
      congrArg (fun L => L (e k)) hd.fderiv
  change (∑ k : Fin 2, fderiv ℝ
    (fun w => test (P w) * (fderiv ℝ P w (e k)) i) z (e k)) = _
  simp_rw [hprod]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, diskBoundaryCoordinate_cofactor_divergence,
    mul_zero, add_zero]
  have hframe : (∑ k : Fin 2, (A (e k)) i • A (e k)) =
      Real.exp (-z 1) ^ 2 • e i := by
    obtain ⟨h0, h1⟩ := diskBoundaryCoordinate_columns p z
    have hn : (P z 0) ^ 2 + (P z 1) ^ 2 = Real.exp (-z 1) ^ 2 := by
      have hh : ‖P z‖ ^ 2 = (P z 0) ^ 2 + (P z 1) ^ 2 := by
        simpa only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using
          EuclideanSpace.norm_sq_eq (P z)
      rw [norm_diskBoundaryCoordinate hp] at hh
      exact hh.symm
    dsimp only [A]
    rw [Fin.sum_univ_two, h0, h1]
    ext j
    fin_cases i <;> fin_cases j <;> norm_num [e, EuclideanSpace.basisFun_apply] <;> nlinarith
  calc
    _ = fderiv ℝ test (P z) (∑ k : Fin 2, (A (e k)) i • A (e k)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ = _ := by rw [hframe, map_smul]; rfl

end PoincareConjecture.M65Boundary
