import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.GradientFrame

set_option autoImplicit false

open scoped InnerProductSpace BigOperators

namespace Poincare.CurvatureIntegral

variable {ι : Type*} [Fintype ι]

theorem matrix_row_sum_lower_bound
    (A : ι → ι → ℝ) {a δ : ℝ} (hδ : 0 ≤ δ)
    (hdiag : ∀ i, a ≤ A i i)
    (hcross : ∀ i j, i ≠ j → |A i j| ≤ δ) (i : ι) :
    a - (Fintype.card ι : ℝ) * δ ≤ ∑ j, A i j := by
  classical
  have hterm (j : ι) : (if i = j then a else 0) - δ ≤ A i j := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      linarith [hdiag i]
    · simp only [if_neg hij, zero_sub]
      exact (abs_le.mp (hcross i j hij)).1
  simpa [Finset.sum_sub_distrib] using
    (Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j)

theorem coefficients_nonpos_of_positive_row_sum
    (A : ι → ι → ℝ) (c : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hrow : ∀ i, 0 < ∑ j, A i j)
    (hpair : ∀ i, ∑ j, A i j * c j ≤ 0) : ∀ i, c i ≤ 0 := by
  classical
  intro i
  by_contra! hi
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ c
    ⟨i, Finset.mem_univ i⟩
  have hpos : 0 < c i₀ := hi.trans_le (hmax i (Finset.mem_univ i))
  have hcompare : (∑ j, A i₀ j) * c i₀ ≤ ∑ j, A i₀ j * c j := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i₀ = j
    · subst j
      exact le_rfl
    · exact mul_le_mul_of_nonpos_left (hmax j (Finset.mem_univ j)) (hoff i₀ j hij)
  have hpositive := mul_pos (hrow i₀) hpos
  linarith [hpair i₀]

theorem coefficients_nonpos_of_diagonal_dominance
    (A : ι → ι → ℝ) (c : ι → ℝ) {a δ : ℝ} (hδ : 0 ≤ δ)
    (hdiag : ∀ i, a ≤ A i i)
    (hcross : ∀ i j, i ≠ j → |A i j| ≤ δ)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hpos : 0 < a - (Fintype.card ι : ℝ) * δ)
    (hpair : ∀ i, ∑ j, A i j * c j ≤ 0) : ∀ i, c i ≤ 0 := by
  apply coefficients_nonpos_of_positive_row_sum A c hoff
  · intro i
    exact hpos.trans_le (matrix_row_sum_lower_bound A hδ hdiag hcross i)
  · exact hpair

theorem coefficients_abs_le_of_diagonal_dominance
    (A : ι → ι → ℝ) (c : ι → ℝ) {a δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdiag : ∀ i, a ≤ A i i)
    (hcross : ∀ i j, i ≠ j → |A i j| ≤ δ)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hpos : 0 < a - (Fintype.card ι : ℝ) * δ)
    (hpair : ∀ i, |∑ j, A i j * c j| ≤ ε) :
    ∀ i, |c i| ≤ ε / (a - (Fintype.card ι : ℝ) * δ) := by
  classical
  let B := ε / (a - (Fintype.card ι : ℝ) * δ)
  have hB : 0 ≤ B := div_nonneg hε hpos.le
  have hbarrier (i : ι) : ε ≤ ∑ j, A i j * B := by
    rw [← Finset.sum_mul]
    calc
      ε = (a - (Fintype.card ι : ℝ) * δ) * B := by
        dsimp [B]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (matrix_row_sum_lower_bound A hδ hdiag hcross i) hB
  have hu : ∀ i, c i - B ≤ 0 := by
    apply coefficients_nonpos_of_diagonal_dominance A (fun i => c i - B)
      hδ hdiag hcross hoff hpos
    intro i
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith [(abs_le.mp (hpair i)).2, hbarrier i]
  have hl : ∀ i, -c i - B ≤ 0 := by
    apply coefficients_nonpos_of_diagonal_dominance A (fun i => -c i - B)
      hδ hdiag hcross hoff hpos
    intro i
    simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    linarith [(abs_le.mp (hpair i)).1, hbarrier i]
  intro i
  change |c i| ≤ B
  exact abs_le.mpr ⟨by linarith [hl i], by linarith [hu i]⟩

theorem sum_abs_coefficients_le_of_diagonal_dominance
    (A : ι → ι → ℝ) (c : ι → ℝ) {a δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdiag : ∀ i, a ≤ A i i)
    (hcross : ∀ i j, i ≠ j → |A i j| ≤ δ)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hpos : 0 < a - (Fintype.card ι : ℝ) * δ)
    (hpair : ∀ i, |∑ j, A i j * c j| ≤ ε) :
    (∑ i, |c i|) ≤ (Fintype.card ι : ℝ) * ε /
      (a - (Fintype.card ι : ℝ) * δ) := by
  have hbound := coefficients_abs_le_of_diagonal_dominance A c
    hδ hε hdiag hcross hoff hpos hpair
  calc
    _ ≤ ∑ _i : ι, ε / (a - (Fintype.card ι : ℝ) * δ) :=
      Finset.sum_le_sum fun i _ => hbound i
    _ = _ := by simp [mul_div_assoc]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gram_pairing_eq_of_orthogonal_decomposition
    (v : ι → E) (c : ι → ℝ) (z zT : E)
    (hdecomp : z = zT + ∑ j, c j • v j)
    (horth : ∀ i, ⟪zT, v i⟫_ℝ = 0) (i : ι) :
    ∑ j, ⟪v i, v j⟫_ℝ * c j = ⟪z, v i⟫_ℝ := by
  rw [hdecomp, inner_add_left, horth i, zero_add, sum_inner]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_left, real_inner_comm (v j) (v i)]
  ring

theorem gram_coefficients_nonpos_of_orthogonal_decomposition
    (v : ι → E) (c : ι → ℝ) (z zT : E) {a δ : ℝ} (hδ : 0 ≤ δ)
    (hdiag : ∀ i, a ≤ ‖v i‖ ^ 2)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ 0)
    (hpos : 0 < a - (Fintype.card ι : ℝ) * δ)
    (hdecomp : z = zT + ∑ j, c j • v j)
    (horth : ∀ i, ⟪zT, v i⟫_ℝ = 0)
    (hz : ∀ i, ⟪z, v i⟫_ℝ ≤ 0) : ∀ i, c i ≤ 0 := by
  apply coefficients_nonpos_of_diagonal_dominance (fun i j => ⟪v i, v j⟫_ℝ) c
    hδ (by simpa only [real_inner_self_eq_norm_sq] using hdiag) hcross hoff hpos
  intro i
  rw [gram_pairing_eq_of_orthogonal_decomposition v c z zT hdecomp horth i]
  exact hz i

theorem gram_coefficients_abs_le_of_orthogonal_decomposition
    (v : ι → E) (c : ι → ℝ) (z zT : E) {a δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdiag : ∀ i, a ≤ ‖v i‖ ^ 2)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ 0)
    (hpos : 0 < a - (Fintype.card ι : ℝ) * δ)
    (hdecomp : z = zT + ∑ j, c j • v j)
    (horth : ∀ i, ⟪zT, v i⟫_ℝ = 0)
    (hz : ∀ i, |⟪z, v i⟫_ℝ| ≤ ε) :
    ∀ i, |c i| ≤ ε / (a - (Fintype.card ι : ℝ) * δ) := by
  apply coefficients_abs_le_of_diagonal_dominance (fun i j => ⟪v i, v j⟫_ℝ) c
    hδ hε (by simpa only [real_inner_self_eq_norm_sq] using hdiag) hcross hoff hpos
  intro i
  rw [gram_pairing_eq_of_orthogonal_decomposition v c z zT hdecomp horth i]
  exact hz i

theorem sum_abs_gram_coefficients_le_of_orthogonal_decomposition
    (v : ι → E) (c : ι → ℝ) (z zT : E) {a δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdiag : ∀ i, a ≤ ‖v i‖ ^ 2)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ 0)
    (hpos : 0 < a - (Fintype.card ι : ℝ) * δ)
    (hdecomp : z = zT + ∑ j, c j • v j)
    (horth : ∀ i, ⟪zT, v i⟫_ℝ = 0)
    (hz : ∀ i, |⟪z, v i⟫_ℝ| ≤ ε) :
    (∑ i, |c i|) ≤ (Fintype.card ι : ℝ) * ε /
      (a - (Fintype.card ι : ℝ) * δ) := by
  have hbound := gram_coefficients_abs_le_of_orthogonal_decomposition v c z zT
    hδ hε hdiag hcross hoff hpos hdecomp horth hz
  calc
    _ ≤ ∑ _i : ι, ε / (a - (Fintype.card ι : ℝ) * δ) :=
      Finset.sum_le_sum fun i _ => hbound i
    _ = _ := by simp [mul_div_assoc]

end Poincare.CurvatureIntegral
