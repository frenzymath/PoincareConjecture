import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.NormBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace PoincareConjecture


theorem abs_multilinear_apply_le_of_inverse_gram_contraction_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (A : MultilinearMap ℝ (fun _ : σ => E) ℝ)
    (b : Module.Basis ι ℝ E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : (∑ i : σ → ι, ∑ j : σ → ι,
      (∏ r, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ (i r) (j r)) *
        A (fun r => b (i r)) * A (fun r => b (j r))) ≤ δ ^ 2)
    (v : σ → E) : |A v| ≤ δ * ∏ r, ‖v r‖ := by
  classical
  let c := stdOrthonormalBasis ℝ E
  have hsum : (∑ a : σ → Fin (Module.finrank ℝ E),
      (A (fun r => c (a r))) ^ 2) ≤ δ ^ 2 := by
    have heq := multilinear_sum_mul_eq_inverse_gram A A b c
    simp only [← sq, ← mul_assoc] at heq
    rw [heq]
    exact hA
  have hsqrt : Real.sqrt (∑ a : σ → Fin (Module.finrank ℝ E),
      (A (fun r => c (a r))) ^ 2) ≤ δ :=
    (Real.sqrt_le_iff).mpr ⟨hδ, hsum⟩
  exact (abs_multilinear_apply_le_orthonormal_tensor_norm A c v).trans
    (mul_le_mul_of_nonneg_right hsqrt (Finset.prod_nonneg fun _ _ => norm_nonneg _))



def bilinearEvaluationTwoTensor
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    MultilinearMap ℝ (fun _ : Fin 2 => E) ℝ where
  toFun v := A (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp



theorem abs_bilinear_apply_self_le_of_inverse_gram_contraction_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (b : Module.Basis ι ℝ E)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : (∑ i : Fin 2 → ι, ∑ j : Fin 2 → ι,
      (∏ r, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ (i r) (j r)) *
        A (b (i 0)) (b (i 1)) * A (b (j 0)) (b (j 1))) ≤ δ ^ 2)
    (v : E) : |A v v| ≤ δ * inner ℝ v v := by
  have h := abs_multilinear_apply_le_of_inverse_gram_contraction_le
    (bilinearEvaluationTwoTensor A) b hδ hA (fun _ => v)
  simpa [bilinearEvaluationTwoTensor, Fin.prod_univ_succ,
    real_inner_self_eq_norm_sq, pow_two] using h

end PoincareConjecture
