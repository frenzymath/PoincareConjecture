import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace PoincareConjecture.M47Positive

theorem exists_gradient_reaction_upper {epsilon beta C : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ R D : ℝ, 0 < R → D ≤ R ^ 2 →
      D / R ^ 2 ≤ C / R ^ epsilon → 960 * R * D - (4 * beta / 3) * R ^ 3 ≤ L := by
  obtain ⟨B0, hB0⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop hepsilon) (720 * C / beta)
  let B := max 1 B0
  have hB : 0 < B := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  refine ⟨960 * B ^ 3, by positivity, ?_⟩
  intro R D hR hD hnormalized
  by_cases hlarge : B ≤ R
  · have hpower : 720 * C / beta ≤ R ^ epsilon :=
      hB0 R ((le_max_right _ _).trans hlarge)
    have hratio : C / R ^ epsilon ≤ beta / 720 := by
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hR epsilon)).mpr
      have h := (div_le_iff₀ hbeta).mp hpower
      nlinarith only [h]
    have hdef := (div_le_iff₀ (sq_pos_of_pos hR)).mp (hnormalized.trans hratio)
    have hmul := mul_le_mul_of_nonneg_left hdef (show 0 ≤ 960 * R by positivity)
    have hnonpos : 960 * R * D - (4 * beta / 3) * R ^ 3 ≤ 0 := by
      nlinarith only [hmul]
    exact hnonpos.trans (by positivity)
  · have hRB : R ≤ B := (lt_of_not_ge hlarge).le
    have hmul := mul_le_mul_of_nonneg_left hD (show 0 ≤ 960 * R by positivity)
    have hcube : R ^ 3 ≤ B ^ 3 := by gcongr
    have hsubtract : 0 ≤ (4 * beta / 3) * R ^ 3 := by positivity
    nlinarith only [hmul, hcube, hsubtract]

theorem exists_linear_cubic_absorption {eta C : ℝ} (heta : 0 < eta) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 0 < R → C * R ≤ eta * R ^ 3 + K := by
  let B := max 1 (C / eta)
  let K := max 1 (C * B)
  have hK : 0 < K := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro R hR
  by_cases hlarge : B ≤ R
  · have hR1 : 1 ≤ R := (le_max_left _ _).trans hlarge
    have hCR : C ≤ R * eta := (div_le_iff₀ heta).mp ((le_max_right _ _).trans hlarge)
    have hsq : R ≤ R ^ 2 := by nlinarith only [hR1, sq_nonneg (R - 1)]
    have hsq' := mul_le_mul_of_nonneg_left hsq heta.le
    have hbound : C ≤ eta * R ^ 2 := by nlinarith only [hCR, hsq']
    have hmul := mul_le_mul_of_nonneg_right hbound hR.le
    nlinarith only [hmul, hK]
  · have hsmall := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hlarge)) hC
    have hCB : C * B ≤ K := le_max_right _ _
    have hcube : 0 ≤ eta * R ^ 3 := by positivity
    linarith only [hsmall, hCB, hcube]

end PoincareConjecture.M47Positive
