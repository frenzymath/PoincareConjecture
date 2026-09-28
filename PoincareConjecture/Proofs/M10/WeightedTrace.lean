import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem trace_eq_sum_normalized_metric {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (C : E ≃L[ℝ] E) (hC : ∀ v w, B (C v) (C w) = inner ℝ v w)
    (A : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E A = ∑ i, B (A (C (b i))) (C (b i)) := by
  rw [← LinearMap.trace_conj' A C.toLinearEquiv.symm,
    LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearEquiv.conj_apply_apply]
  change inner ℝ (b i) (C.symm (A (C (b i)))) = _
  have h := hC (C.symm (A (C (b i)))) (b i)
  simpa only [ContinuousLinearEquiv.apply_symm_apply, real_inner_comm] using h.symm

theorem trace_fderiv_smul {ρ : E → ℝ} {a : E → E} {y : E}
    (hρ : DifferentiableAt ℝ ρ y) (ha : DifferentiableAt ℝ a y) :
    LinearMap.trace ℝ E (fderiv ℝ (fun z ↦ ρ z • a z) y).toLinearMap =
      ρ y * LinearMap.trace ℝ E (fderiv ℝ a y).toLinearMap +
        fderiv ℝ ρ y (a y) := by
  rw [fderiv_fun_smul hρ ha, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul]
  change ρ y * LinearMap.trace ℝ E (fderiv ℝ a y).toLinearMap +
      LinearMap.trace ℝ E ((fderiv ℝ ρ y).toLinearMap.smulRight (a y)) = _
  rw [LinearMap.trace_smulRight]
  rfl

end PoincareConjecture.M10
