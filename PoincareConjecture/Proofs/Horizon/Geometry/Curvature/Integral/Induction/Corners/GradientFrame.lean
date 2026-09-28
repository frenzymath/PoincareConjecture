import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse










set_option autoImplicit false

open scoped InnerProductSpace BigOperators

namespace Poincare.CurvatureIntegral



theorem norm_lower_bound_of_opposite_pair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) {δ : ℝ} (hw : ‖w‖ ≤ 1)
    (hopposite : ⟪v, w⟫_ℝ ≤ -1 + 2 * δ) :
    1 - 2 * δ ≤ ‖v‖ := by
  have hCS := abs_real_inner_le_norm v w
  have hupper := mul_le_mul_of_nonneg_left hw (norm_nonneg v)
  nlinarith [neg_le_abs ⟪v, w⟫_ℝ]


theorem strainer_parameter_bounds (k : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1))) :
    δ < 1 / 2 ∧ (k : ℝ) * δ < (1 - 2 * δ) ^ 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * ((k : ℝ) + 1))).mp hsmall
  have hproduct : 0 ≤ (k : ℝ) * δ := mul_nonneg hk hδ
  constructor <;> nlinarith [sq_nonneg δ]



theorem linearIndependent_of_strainer_pairs
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (v w : ι → E) {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hsmall : (Fintype.card ι : ℝ) * δ < (1 - 2 * δ) ^ 2)
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hopposite : ∀ i, ⟪v i, w i⟫_ℝ ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ) :
    LinearIndependent ℝ v := by
  classical
  have hnorm (i : ι) : 1 - 2 * δ ≤ ‖v i‖ :=
    norm_lower_bound_of_opposite_pair (v i) (w i) (hw i) (hopposite i)
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i, ‖Matrix.gram ℝ v i j‖) ≤
      (Fintype.card ι : ℝ) * δ := by
    have hcard : ((Finset.univ.erase i).card : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset i (Finset.univ : Finset ι))
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, δ := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [Matrix.gram_apply, Real.norm_eq_abs] using
          hcross i j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = ((Finset.univ.erase i).card : ℝ) * δ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hδ
  have hdiag : (1 - 2 * δ) ^ 2 ≤ ‖Matrix.gram ℝ v i i‖ := by
    simpa only [Matrix.gram_apply, real_inner_self_eq_norm_sq,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v i‖)] using
      (sq_le_sq₀ (by linarith : 0 ≤ 1 - 2 * δ) (norm_nonneg (v i))).mpr (hnorm i)
  exact (hsum.trans_lt hsmall).trans_le hdiag


theorem surjective_inner_family_of_linearIndependent
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    {v : ι → E} (hv : LinearIndependent ℝ v) :
    Function.Surjective (fun x : E => fun i => ⟪v i, x⟫_ℝ) := by
  classical
  have hunit : IsUnit (Matrix.gram ℝ v) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv))
  intro a
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit a
  refine ⟨∑ i, c i • v i, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, inner_sum, inner_smul_right,
    mul_comm] using congrFun hc i

end Poincare.CurvatureIntegral
