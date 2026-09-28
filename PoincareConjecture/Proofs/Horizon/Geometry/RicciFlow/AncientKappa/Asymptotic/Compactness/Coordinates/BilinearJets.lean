import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.HolderAssembly
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas








set_option autoImplicit false

open scoped ContDiff BigOperators

namespace Poincare.Analysis.Calculus

theorem norm_iteratedFDeriv_bilinear_le_of_entries
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {x : E} (hA : ContDiffAt ℝ ∞ A x) (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i j : Fin n, ‖iteratedFDeriv ℝ m (fun y ↦
      A y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ m A x‖ ≤ (n : ℝ) ^ 2 * C := by
  have hm : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hprod : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (by simp)
  have h := PoincareConjecture.HarmonicCoordinates.norm_bilinear_le_dim_sq_mul_of_entries
    (iteratedFDeriv ℝ m A x v) (mul_nonneg hC hprod) (fun i j ↦ ?_)
  · simpa only [mul_assoc] using h
  · let ev :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (EuclideanSpace.basisFun (Fin n) ℝ i))
    have heq := congrArg (fun T ↦ T v) (ev.iteratedFDeriv_comp_left hA hm)
    change iteratedFDeriv ℝ m (fun y ↦
        A y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x v =
      iteratedFDeriv ℝ m A x v (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) at heq
    rw [← heq, ← Real.norm_eq_abs]
    exact (ContinuousMultilinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right (hbound i j) hprod)

end Poincare.Analysis.Calculus
