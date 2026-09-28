import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Finite







set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


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
