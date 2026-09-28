import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ} {W : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem norm_principal_equivalent_inclusion_le_one
    {K : Set V} (hK : IsClosed K) (A : Fin n → Fin n → 𝓢(V, ℝ))
    {ell : ℝ} (hell : 0 < ell)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (e : W ≃L[ℝ] dirichletForm K)
    (hnorm : ∀ u : W, principalFormPairing K A (e u) (e u) = ‖u‖ ^ 2) :
    ‖(dirichletInclusion K).comp e.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  have hE : 0 ≤ principalEnergy K A (e u) (e u) :=
    (mul_nonneg hell.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans
      (principalEnergy_coercive hK A hEll (e u))
  have hs : ‖dirichletInclusion K (e u)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [← hnorm u]
    simp only [principalFormPairing, real_inner_self_eq_norm_sq]
    linarith only [hE]
  simpa only [one_mul, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using!
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem norm_principal_equivalence_le
    {K : Set V} (hK : IsClosed K) (A : Fin n → Fin n → 𝓢(V, ℝ))
    {ell M : ℝ} (hM : 0 ≤ M) (hscale : 1 ≤ min 1 ell * M ^ 2)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (e : W ≃L[ℝ] dirichletForm K)
    (hnorm : ∀ u : W, principalFormPairing K A (e u) (e u) = ‖u‖ ^ 2) :
    ‖e.toContinuousLinearMap‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro u
  have hc := principalFormPairing_coercive hK A hEll (e u)
  rw [hnorm u] at hc
  have h1 := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖e u‖)
  have h2 := mul_le_mul_of_nonneg_left hc (sq_nonneg M)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg u))).mp
  change ‖e u‖ ^ 2 ≤ (M * ‖u‖) ^ 2
  nlinarith only [h1, h2]

end PoincareConjecture.M35.Uniqueness.Heat
