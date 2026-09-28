import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckComparison











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)



theorem roundCylinderGram_chart_center_inv_le_one {u : ℝ} (hu : u ≤ 0)
    (q : UnitTwoSphere) (s : ℝ) (a b : Fin 3) :
    |(roundCylinderGram u (chartAt E₂ q) (chartAt E₂ q q, s))⁻¹ a b| ≤ 1 := by
  have hu1 : u < 1 := hu.trans_lt zero_lt_one
  have hpos : 0 < 2 * (1 - u) := mul_pos two_pos (sub_pos.mpr hu1)
  have hinv : (2 * (1 - u))⁻¹ ≤ 1 := by
    simpa only [inv_one] using inv_anti₀ zero_lt_one (by linarith : 1 ≤ 2 * (1 - u))
  rw [roundCylinderGram_chart_center_inv hu1.ne q s, Matrix.diagonal_apply]
  split_ifs with hab
  · subst b
    fin_cases a
    · exact (abs_of_pos (inv_pos.mpr hpos)).trans_le hinv
    · exact (abs_of_pos (inv_pos.mpr hpos)).trans_le hinv
    · norm_num
  · norm_num



theorem roundCylinderJetErrorSquared_le_of_component_difference
    {u : ℝ} (hu : u ≤ 0) (B D : RoundCylinderTwoTensor) (m : ℕ)
    (z : RoundCylinderSpace) {eta : ℝ}
    (hjet : ∀ k ≤ m, ∀ a : Fin (2 + k) → Fin 3,
      |roundCylinderIteratedDerivative u (chartAt E₂ z.1) B k
          (chartAt E₂ z.1 z.1, z.2) a -
        roundCylinderIteratedDerivative u (chartAt E₂ z.1) D k
          (chartAt E₂ z.1 z.1, z.2) a| ≤ eta) :
    roundCylinderJetErrorSquared u B m z ≤
      2 * roundCylinderJetErrorSquared u D m z +
      2 * (∑ k ∈ Finset.range (m + 1), ((3 : ℝ) ^ (2 + k)) ^ 2) * eta ^ 2 := by
  apply (roundCylinderJetErrorSquared_le_two_mul (hu.trans_lt zero_lt_one) B D m z).trans
  apply add_le_add_right
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  simpa only [one_pow, mul_one] using roundCylinderTensorNormSquared_le
    (chartAt E₂ z.1) (chartAt E₂ z.1 z.1, z.2)
    (fun a => roundCylinderIteratedDerivative u (chartAt E₂ z.1) B k
        (chartAt E₂ z.1 z.1, z.2) a -
      roundCylinderIteratedDerivative u (chartAt E₂ z.1) D k
        (chartAt E₂ z.1 z.1, z.2) a)
    (M := 1) zero_le_one (roundCylinderGram_chart_center_inv_le_one hu z.1 z.2)
    (hjet k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))





theorem exists_roundCylinderFamilyClose_perturbation_tolerance
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ {delta : ℝ}, 0 < delta → delta ≤ epsilon / 4 →
      ∀ {I : Set ℝ}, (∀ u ∈ I, u ≤ 0) →
      ∀ (B D : ℝ → RoundCylinderTwoTensor),
      RoundCylinderFamilyClose delta I D →
      (∀ u ∈ I, RoundCylinderTensorSmoothOn epsilon (B u)) →
      (∀ u ∈ I, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ∀ k ≤ ⌊epsilon⁻¹⌋₊, ∀ a : Fin (2 + k) → Fin 3,
          |roundCylinderIteratedDerivative u (chartAt E₂ z.1) (B u) k
              (chartAt E₂ z.1 z.1, z.2) a -
            roundCylinderIteratedDerivative u (chartAt E₂ z.1) (D u) k
              (chartAt E₂ z.1 z.1, z.2) a| ≤ eta) →
      RoundCylinderFamilyClose epsilon I B := by
  let m : ℕ := ⌊epsilon⁻¹⌋₊
  let W : ℝ := ∑ k ∈ Finset.range (m + 1), ((3 : ℝ) ^ (2 + k)) ^ 2
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  let eta : ℝ := epsilon / (4 * (W + 1))
  have heta : 0 < eta := div_pos hepsilon (by positivity)
  have hscaled : 4 * (W + 1) * eta = epsilon := by
    dsimp [eta]
    field_simp
  have hsquare : 16 * (W + 1) ^ 2 * eta ^ 2 = epsilon ^ 2 := by
    calc
      _ = (4 * (W + 1) * eta) ^ 2 := by ring
      _ = epsilon ^ 2 := by rw [hscaled]
  have hsmall : 2 * W * eta ^ 2 ≤ epsilon ^ 2 / 2 := by
    have hw : 2 * W ≤ 8 * (W + 1) ^ 2 := by nlinarith [sq_nonneg W]
    have h := mul_le_mul_of_nonneg_right hw (sq_nonneg eta)
    nlinarith
  refine ⟨eta, heta, ?_⟩
  intro delta hdelta hde I hI B D hD hs hj
  obtain ⟨_, b, hb, hbound⟩ := hD
  have hdε : delta ≤ epsilon := by linarith
  have hinv := inv_anti₀ hdelta hdε
  have hδsq : delta ^ 2 ≤ (epsilon / 4) ^ 2 := pow_le_pow_left₀ hdelta.le hde 2
  refine ⟨hs, 2 * b + 2 * W * eta ^ 2, ?_, ?_⟩
  · nlinarith [sq_pos_of_pos hepsilon]
  · intro u hu z hz
    apply (roundCylinderJetErrorSquared_le_of_component_difference (hI u hu)
      (B u) (D u) m z (hj u hu z hz)).trans
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    exact (roundCylinderJetErrorSquared_mono_order ((hI u hu).trans_lt zero_lt_one)
      (D u) (Nat.floor_mono hinv) z).trans
      (hbound u hu z ⟨lt_of_le_of_lt (neg_le_neg hinv) hz.1, hz.2.trans_le hinv⟩)

end PoincareConjecture.M34
