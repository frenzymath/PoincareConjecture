import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularSource
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

def m64TriangularDerivative (a b : ℝ) : LoopPlane →L[ℝ] LoopPlane :=
  (a • (EuclideanSpace.proj 0 : LoopPlane →L[ℝ] ℝ) +
    b • (EuclideanSpace.proj 1 : LoopPlane →L[ℝ] ℝ)).smulRight e0 +
    (EuclideanSpace.proj 1 : LoopPlane →L[ℝ] ℝ).smulRight e1

theorem m64TriangularDerivative_apply (a b : ℝ) (v : LoopPlane) :
    m64TriangularDerivative a b v = annulusPoint (a * v 0 + b * v 1) (v 1) := by
  ext i
  fin_cases i <;> simp [m64TriangularDerivative, annulusPoint]

theorem m64TriangularDerivative_det (a b : ℝ) : (m64TriangularDerivative a b).det = a := by
  change LinearMap.det (m64TriangularDerivative a b).toLinearMap = a
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, m64TriangularDerivative_apply, annulusPoint]

theorem m64TriangularSource_second_derivative
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    (hsecond : ∀ p, T p 1 = p 1) (p v : LoopPlane) : fderiv ℝ T p v 1 = v 1 := by
  let L : LoopPlane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hfun : L ∘ T = L := funext hsecond
  have hd := (L.hasFDerivAt.comp p (hT p).hasFDerivAt).fderiv
  rw [hfun, L.fderiv] at hd
  exact (congrArg (fun A : LoopPlane →L[ℝ] ℝ => A v) hd).symm

theorem m64TriangularSource_fderiv
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    (hsecond : ∀ p, T p 1 = p 1) (p : LoopPlane) :
    fderiv ℝ T p = m64TriangularDerivative (fderiv ℝ T p e0 0) (fderiv ℝ T p e1 0) := by
  ext v i
  have hv : v = v 0 • e0 + v 1 • e1 := by
    ext j
    fin_cases j <;> simp
  fin_cases i
  · rw [m64TriangularDerivative_apply]
    change fderiv ℝ T p v 0 = fderiv ℝ T p e0 0 * v 0 + fderiv ℝ T p e1 0 * v 1
    conv_lhs => rw [hv, map_add, map_smul, map_smul]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · rw [m64TriangularDerivative_apply]
    exact m64TriangularSource_second_derivative hT hsecond p v

theorem m64TriangularSource_det
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    (hsecond : ∀ p, T p 1 = p 1) (p : LoopPlane) :
    (fderiv ℝ T p).det = fderiv ℝ T p e0 0 := by
  calc
    _ = (m64TriangularDerivative (fderiv ℝ T p e0 0) (fderiv ℝ T p e1 0)).det :=
      congrArg (fun A : LoopPlane →L[ℝ] LoopPlane => A.det)
        (m64TriangularSource_fderiv hT hsecond p)
    _ = _ := m64TriangularDerivative_det _ _

theorem m64TriangularSource_inverse_second
    (T : LoopPlane ≃ₜ LoopPlane) (hsecond : ∀ p, T p 1 = p 1) (p : LoopPlane) :
    T.symm p 1 = p 1 := by
  simpa only [Homeomorph.apply_symm_apply] using (hsecond (T.symm p)).symm

theorem m64TriangularSource_inverse_derivative
    (T : LoopPlane ≃ₜ LoopPlane) (hT : Differentiable ℝ T)
    (hi : Differentiable ℝ T.symm) (hsecond : ∀ p, T p 1 = p 1) (p : LoopPlane) :
    fderiv ℝ T.symm (T p) e0 0 * fderiv ℝ T p e0 0 = 1 ∧
      fderiv ℝ T.symm (T p) e0 0 * fderiv ℝ T p e1 0 +
        fderiv ℝ T.symm (T p) e1 0 = 0 := by
  have hfun : T.symm ∘ T = id := by funext q; simp
  have hd := ((hi (T p)).hasFDerivAt.comp p (hT p).hasFDerivAt).fderiv
  rw [hfun, fderiv_id] at hd
  have hcalc (i : Fin 2) := congrArg (fun A : LoopPlane →L[ℝ] LoopPlane =>
    A (EuclideanSpace.single i 1) 0) hd
  rw [m64TriangularSource_fderiv hT hsecond,
    m64TriangularSource_fderiv hi (m64TriangularSource_inverse_second T hsecond)] at hcalc
  constructor
  · simpa [ContinuousLinearMap.comp_apply, m64TriangularDerivative_apply, annulusPoint]
      using (hcalc 0).symm
  · simpa [ContinuousLinearMap.comp_apply, m64TriangularDerivative_apply, annulusPoint]
      using (hcalc 1).symm

end PoincareConjecture
