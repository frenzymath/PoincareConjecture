import PoincareConjecture.Proofs.M34.Mathlib.NeckDiagonalContraction
import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderJetErrorBound

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem roundCylinderTensorNormSquared_chart_center_nonneg
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, s) T := by
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_chart_center_inv hu.ne q s]
  apply diagonal_tensor_contraction_nonneg
  intro i
  fin_cases i
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hu.le))
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hu.le))
  · norm_num

theorem roundCylinderJetErrorSquared_nonneg {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) (order : ℕ) (z : RoundCylinderSpace) :
    0 ≤ roundCylinderJetErrorSquared u B order z := by
  unfold roundCylinderJetErrorSquared
  exact Finset.sum_nonneg fun _ _ =>
    roundCylinderTensorNormSquared_chart_center_nonneg hu _ _ _

theorem roundCylinderJetErrorSquared_mono_order {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) {m n : ℕ} (hmn : m ≤ n) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u B m z ≤ roundCylinderJetErrorSquared u B n z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hmn 1))
  intro k _ _
  exact roundCylinderTensorNormSquared_chart_center_nonneg hu _ _ _

theorem roundCylinderTensorNormSquared_chart_center_le
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T S : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, s) T ≤
      2 * roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, s) S +
      2 * roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, s)
        (fun a => T a - S a) := by
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_chart_center_inv hu.ne q s]
  apply diagonal_tensor_contraction_le
  intro i
  fin_cases i
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hu.le))
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hu.le))
  · norm_num

theorem roundCylinderJetErrorSquared_le_two_mul
    {u : ℝ} (hu : u < 1) (B D : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u B order z ≤
      2 * roundCylinderJetErrorSquared u D order z +
      2 * ∑ k ∈ Finset.range (order + 1),
        roundCylinderTensorNormSquared u (chartAt E₂ z.1) (chartAt E₂ z.1 z.1, z.2)
          (fun a =>
            roundCylinderIteratedDerivative u (chartAt E₂ z.1) B k
              (chartAt E₂ z.1 z.1, z.2) a -
            roundCylinderIteratedDerivative u (chartAt E₂ z.1) D k
              (chartAt E₂ z.1 z.1, z.2) a) := by
  unfold roundCylinderJetErrorSquared
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ =>
    roundCylinderTensorNormSquared_chart_center_le hu _ _ _ _

end PoincareConjecture.M34

namespace PoincareConjecture

theorem RoundCylinderTensorSmoothOn.mono_epsilon {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hde : delta ≤ epsilon) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn delta B) :
    RoundCylinderTensorSmoothOn epsilon B := by
  have hinv : epsilon⁻¹ ≤ delta⁻¹ := inv_anti₀ hdelta hde
  intro q a b
  exact (hB q a b).mono fun p hp =>
    ⟨hp.1, lt_of_le_of_lt (neg_le_neg hinv) hp.2.1, hp.2.2.trans_le hinv⟩

theorem RoundCylinderClose.mono_epsilon {delta epsilon u : ℝ}
    (hdelta : 0 < delta) (hde : delta ≤ epsilon) (hu : u < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose delta u B) :
    RoundCylinderClose epsilon u B := by
  obtain ⟨hsmooth, b, hb, hjet⟩ := hB
  have hinv : epsilon⁻¹ ≤ delta⁻¹ := inv_anti₀ hdelta hde
  refine ⟨hsmooth.mono_epsilon hdelta hde, b,
    hb.trans_le (pow_le_pow_left₀ hdelta.le hde 2), ?_⟩
  intro z hz
  exact (M34.roundCylinderJetErrorSquared_mono_order hu B
    (Nat.floor_mono hinv) z).trans (hjet z
      ⟨lt_of_le_of_lt (neg_le_neg hinv) hz.1, hz.2.trans_le hinv⟩)

theorem RoundCylinderFamilyClose.mono_epsilon {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hde : delta ≤ epsilon) {I : Set ℝ}
    (hI : ∀ u ∈ I, u < 1) {B : ℝ → RoundCylinderTwoTensor}
    (hB : RoundCylinderFamilyClose delta I B) :
    RoundCylinderFamilyClose epsilon I B := by
  obtain ⟨hsmooth, b, hb, hjet⟩ := hB
  have hinv : epsilon⁻¹ ≤ delta⁻¹ := inv_anti₀ hdelta hde
  refine ⟨fun u hu => (hsmooth u hu).mono_epsilon hdelta hde, b,
    hb.trans_le (pow_le_pow_left₀ hdelta.le hde 2), ?_⟩
  intro u hu z hz
  exact (M34.roundCylinderJetErrorSquared_mono_order (hI u hu) (B u)
    (Nat.floor_mono hinv) z).trans (hjet u hu z
      ⟨lt_of_le_of_lt (neg_le_neg hinv) hz.1, hz.2.trans_le hinv⟩)

end PoincareConjecture
