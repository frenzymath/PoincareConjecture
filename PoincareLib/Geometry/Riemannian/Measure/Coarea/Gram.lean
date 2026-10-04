import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Matrix.PosDef

/-!
# The Gram determinant identity for regular coarea

In coordinates whose first coordinate is the level function, its gradient is
metric-dual to the first coordinate covector. Cramer's rule identifies its
squared length times the ambient Gram determinant with the tangential minor.
This is the density calculation for Petrunin, Section 2.2, manuscript p. 4.
-/

set_option autoImplicit false

open Matrix Module
open scoped BigOperators InnerProductSpace

namespace Poincare.Coarea

/-- Cramer's rule for the first coordinate and its complementary minor. -/
lemma det_mul_first_eq_minor {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin (n + 1) → ℝ) (hv : G *ᵥ v = Pi.single 0 1) :
    G.det * v 0 = (G.submatrix Fin.succ Fin.succ).det := by
  have h := congrArg (fun w : Fin (n + 1) → ℝ => (G.adjugate *ᵥ w) 0) hv
  rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec] at h
  simpa [mulVec_single, adjugate_fin_succ_eq_det_submatrix] using h

/-- The norm of the dual first-coordinate vector gives the ratio of the
tangential and ambient Gram determinants. -/
theorem gram_det_mul_inner_dual {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Basis (Fin (n + 1)) ℝ E) (z : E)
    (hz : ∀ i, ⟪z, b i⟫_ℝ = if i = 0 then 1 else 0) :
    (Matrix.gram ℝ b).det * ⟪z, z⟫_ℝ =
      (Matrix.gram ℝ (fun i : Fin n => b i.succ)).det := by
  have hG : Matrix.gram ℝ b *ᵥ b.repr z = Pi.single 0 1 := by
    ext i
    change (∑ j, ⟪b i, b j⟫_ℝ * b.repr z j) = _
    rw [show (∑ j, ⟪b i, b j⟫_ℝ * b.repr z j) = ⟪b i, z⟫_ℝ by
      conv_rhs => rw [← b.sum_repr z]
      simp only [inner_sum, inner_smul_right, mul_comm]]
    rw [real_inner_comm, hz]
    simp [Pi.single_apply]
  have hnorm : ⟪z, z⟫_ℝ = b.repr z 0 := by
    conv_lhs => rhs; rw [← b.sum_repr z]
    simp only [inner_sum, inner_smul_right, hz, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hnorm]
  exact det_mul_first_eq_minor (Matrix.gram ℝ b) (b.repr z) hG

/-- The positive square-root form is the volume-density identity in regular
level coordinates, including zero-dimensional levels. -/
theorem sqrt_gram_det_mul_norm_dual {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Basis (Fin (n + 1)) ℝ E) (z : E)
    (hz : ∀ i, ⟪z, b i⟫_ℝ = if i = 0 then 1 else 0) :
    Real.sqrt (Matrix.gram ℝ b).det * ‖z‖ =
      Real.sqrt (Matrix.gram ℝ (fun i : Fin n => b i.succ)).det := by
  have hdet : 0 ≤ (Matrix.gram ℝ b).det :=
    (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.le
  rw [← Real.sqrt_sq (norm_nonneg z), ← real_inner_self_eq_norm_sq,
    ← Real.sqrt_mul hdet, gram_det_mul_inner_dual b z hz]

end Poincare.Coarea
