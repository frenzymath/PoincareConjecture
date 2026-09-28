import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactSlices
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Coefficients
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations











noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff RealInnerProductSpace BigOperators

namespace Poincare.Parabolic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_fderiv_smul_apply {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => χ y • f y)) x v w =
      χ x • fderiv ℝ (fderiv ℝ f) x v w +
      fderiv ℝ χ x v • fderiv ℝ f x w +
      fderiv ℝ χ x w • fderiv ℝ f x v +
      fderiv ℝ (fderiv ℝ χ) x v w • f x := by
  have hχd := hχ.differentiable (by simp)
  have hfd := hf.differentiable (by simp)
  have hdχ := (hχ.fderiv_right (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))).differentiable (by simp)
  have hdf := (hf.fderiv_right (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))).differentiable (by simp)
  have h₁ := (hχd x).hasFDerivAt.smul (hdf x).hasFDerivAt
  have h₂ := (ContinuousLinearMap.smulRightL ℝ E F).hasFDerivAt_of_bilinear
    (hdχ x).hasFDerivAt (hfd x).hasFDerivAt
  have heq : fderiv ℝ (fun y => χ y • f y) =
      fun y => χ y • fderiv ℝ f y + (fderiv ℝ χ y).smulRight (f y) := by
    funext y
    exact fderiv_fun_smul (hχd y) (hfd y)
  rw [heq]
  have hsum := h₁.add h₂
  have hsumeq := hsum.fderiv
  change fderiv ℝ (fun y => χ y • fderiv ℝ f y + (fderiv ℝ χ y).smulRight (f y)) x = _ at hsumeq
  rw [hsumeq]
  simp [ContinuousLinearMap.precompR, add_assoc]



theorem norm_hessian_smul_sub_le {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun y => χ y • f y)) x -
      χ x • fderiv ℝ (fderiv ℝ f) x‖ ≤
      2 * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ f x‖ +
        ‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖f x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  simp only [_root_.sub_apply, _root_.smul_apply,
    fderiv_fderiv_smul_apply hχ hf]
  have heq : χ x • fderiv ℝ (fderiv ℝ f) x v w +
      fderiv ℝ χ x v • fderiv ℝ f x w +
      fderiv ℝ χ x w • fderiv ℝ f x v +
      fderiv ℝ (fderiv ℝ χ) x v w • f x - χ x • fderiv ℝ (fderiv ℝ f) x v w =
      fderiv ℝ χ x v • fderiv ℝ f x w + fderiv ℝ χ x w • fderiv ℝ f x v +
      fderiv ℝ (fderiv ℝ χ) x v w • f x := by abel
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ χ x v • fderiv ℝ f x w‖ + ‖fderiv ℝ χ x w • fderiv ℝ f x v‖ +
        ‖fderiv ℝ (fderiv ℝ χ) x v w • f x‖ := norm_add₃_le
    _ ≤ (‖fderiv ℝ χ x‖ * ‖v‖) * (‖fderiv ℝ f x‖ * ‖w‖) +
        (‖fderiv ℝ χ x‖ * ‖w‖) * (‖fderiv ℝ f x‖ * ‖v‖) +
        ((‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖v‖) * ‖w‖) * ‖f x‖ := by
      simp only [norm_smul]
      gcongr <;> first | exact ContinuousLinearMap.le_opNorm _ _ |
        exact ContinuousLinearMap.le_opNorm₂ _ _ _
    _ = _ := by ring

theorem timeDerivative_smul {χ : E × ℝ → ℝ} {f : E × ℝ → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (p : E × ℝ) :
    timeDerivative (fun q => χ q • f q) p =
      χ p • timeDerivative f p + timeDerivative χ p • f p := by
  have h := (hasDerivAt_timeSlice (hχ.differentiable (by simp)) p.1 p.2).smul
    (hasDerivAt_timeSlice (hf.differentiable (by simp)) p.1 p.2)
  exact (hasDerivAt_timeSlice ((hχ.smul hf).differentiable (by simp)) p.1 p.2).unique h

section Principal

variable {ι : Type*} [Fintype ι]


theorem norm_principal_cutoff_commutator_le
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    {χ : EuclideanSpace ℝ ι → ℝ} {f : EuclideanSpace ℝ ι → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ ι) :
    ‖∑ i : ι, ∑ j : ι,
      inner ℝ (EuclideanSpace.basisFun ι ℝ i) (a (EuclideanSpace.basisFun ι ℝ j)) •
        (fderiv ℝ (fderiv ℝ (fun y => χ y • f y)) x -
          χ x • fderiv ℝ (fderiv ℝ f) x)
          (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)‖ ≤
      (Fintype.card ι : ℝ) ^ 2 * ‖a‖ *
        (2 * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ f x‖ +
          ‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖f x‖) := by
  exact (norm_principal_contraction_le a _).trans
    (mul_le_mul_of_nonneg_left (norm_hessian_smul_sub_le hχ hf x) (by positivity))

end Principal

end Poincare.Parabolic.Interior
