import PoincareLib.Geometry.RicciFlow.Harnack.Finite

/-!
# Scalar Harnack from Hamilton block positivity

The trace of the lower diagonal block gives the scalar Harnack expression
for an arbitrary elapsed time, using Lean's total division also at zero.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The trace of the Hamilton block is nonnegative in the vector-zero case. -/
lemma scalar_harnack_nonneg_of_hamiltonBlockPos
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) {t : ℝ}
    (_ht : t ∈ Set.Ioo T₀ T₁) (x : M) (τ : ℝ)
    (hblock : HamiltonBlockPos F t x τ) :
    0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x + (F.connection t).scalarCurvature x / τ := by
  have hsum : 0 ≤ ∑ i, hamiltonM (F.connection t) τ x
      ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x i) := by
    apply Finset.sum_nonneg
    intro i _
    exact Matrix.PosSemidef.diag_nonneg hblock (i := Sum.inr i)
  calc
    0 ≤ 2 * (∑ i, hamiltonM (F.connection t) τ x
        ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x i)) :=
      mul_nonneg (by norm_num) hsum
    _ = _ := by
      rw [hamiltonM_trace (F.connection t)
        (hC.tensor_calculus n M (F.metric t) (F.connection t)) τ x]
      ring

end Poincare.RicciFlow.Harnack
