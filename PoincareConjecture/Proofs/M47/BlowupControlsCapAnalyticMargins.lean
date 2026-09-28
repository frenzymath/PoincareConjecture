import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticTolerance

set_option autoImplicit false

open Set

namespace PoincareConjecture.M47

theorem exists_cap_scalar_ratio_margin {m b C : ℝ}
    (hm : 0 < m) (hb : 1 ≤ b) (hbC : b < C) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ b' : ℝ, b' < C ∧
      ∀ R S R' S' : ℝ, m ≤ R → S ≤ b * R →
      |R' - R| ≤ nu → |S' - S| ≤ nu → 0 < R' ∧ S' ≤ b' * R' := by
  let nu := min (m / 2) ((C - b) * m / (4 * (b + 1)))
  have hgap : 0 < C - b := sub_pos.mpr hbC
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hnu : 0 < nu :=
    lt_min (half_pos hm) (div_pos (mul_pos hgap hm) (by positivity))
  have hnum : nu ≤ m / 2 := min_le_left _ _
  have hnub : (b + 1) * nu ≤ (C - b) * m / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (b + 1))).mp
      (min_le_right (m / 2) ((C - b) * m / (4 * (b + 1))))
    change nu * (4 * (b + 1)) ≤ (C - b) * m at h
    nlinarith
  refine ⟨nu, hnu, (C + b) / 2, by linarith, ?_⟩
  intro R S R' S' hR hratio hdiffR hdiffS
  have hRlow := (abs_le.mp hdiffR).1
  have hSup := (abs_le.mp hdiffS).2
  have hfloor : m / 2 ≤ R' := by linarith
  have hgain := mul_le_mul_of_nonneg_left hfloor hgap.le
  have hmove := mul_le_mul_of_nonneg_left hRlow hbpos.le
  exact ⟨(half_pos hm).trans_le hfloor, by nlinarith⟩

theorem exists_cap_power_margin {m M b C p : ℝ}
    (hm : 0 < m) (hb : 0 ≤ b) (hbC : b < C) (hp : 0 ≤ p) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ b' : ℝ, 0 < b' ∧ b' < C ∧
      ∀ R ∈ Icc m M, ∀ A R' A' : ℝ, A ≤ b * R ^ p →
      |R' - R| ≤ nu → |A' - A| ≤ nu → 0 < R' ∧ A' ≤ b' * R' ^ p := by
  let b' := (b + C) / 2
  have hb' : 0 < b' := by dsimp [b']; linarith
  have hb'C : b' < C := by dsimp [b']; linarith
  have hgap : 0 < b' - b := by dsimp [b']; linarith
  let c := (b' - b) * m ^ p
  have hc : 0 < c := mul_pos hgap (Real.rpow_pos_of_pos hm p)
  have hu : UniformContinuousOn (fun r : ℝ => r ^ p) (Icc (m / 2) (M + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (Real.continuous_rpow_const hp).continuousOn
  obtain ⟨delta, hdelta, hpower⟩ := Metric.uniformContinuousOn_iff_le.mp hu
    (c / (4 * b')) (div_pos hc (by positivity))
  let nu := min (m / 2) (min 1 (min delta (c / 4)))
  have hnu : 0 < nu := lt_min (half_pos hm)
    (lt_min zero_lt_one (lt_min hdelta (by positivity)))
  have hnum : nu ≤ m / 2 := min_le_left _ _
  have hnu1 : nu ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hnud : nu ≤ delta := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hnuc : nu ≤ c / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨nu, hnu, b', hb', hb'C, ?_⟩
  intro R hR A R' A' hbound hdiffR hdiffA
  have hRnear := abs_le.mp hdiffR
  have hRold : R ∈ Icc (m / 2) (M + 1) := by
    constructor <;> linarith [hR.1, hR.2]
  have hRnew : R' ∈ Icc (m / 2) (M + 1) := by
    constructor <;> linarith [hR.1, hR.2, hRnear.1, hRnear.2]
  have hpow : |R' ^ p - R ^ p| ≤ c / (4 * b') := by
    simpa only [Real.dist_eq] using hpower R' hRnew R hRold
      (by simpa only [Real.dist_eq] using hdiffR.trans hnud)
  have hscaled := mul_le_mul_of_nonneg_left (abs_le.mp hpow).1 hb'.le
  have hcancel : b' * (c / (4 * b')) = c / 4 := by
    field_simp [hb'.ne']
  have hgain := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm.le hR.1 hp) hgap.le
  change c ≤ (b' - b) * R ^ p at hgain
  have hAup := (abs_le.mp hdiffA).2
  exact ⟨(half_pos hm).trans_le hRnew.1, by nlinarith⟩

end PoincareConjecture.M47
