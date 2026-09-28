import PoincareConjecture.Proofs.M47.BlowupControlsFirstFailure










set_option autoImplicit false

open Set

namespace PoincareConjecture.M47


theorem exists_source_initial_search_duration {A m : ℝ} (hA : 0 < A) (hm : 0 < m) :
    ∃ L d : ℝ, 1 ≤ L ∧ 2 / m ≤ L ∧ 0 < d ∧ d ≤ m ∧ d ≤ 1 ∧
      64 * A * L * (2 * d) ≤ 1 := by
  let L := max 1 (2 / m)
  let d := min m (min 1 (128 * A * L)⁻¹)
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hcoef : 0 < 128 * A * L := by positivity
  have hd : 0 < d := lt_min hm (lt_min zero_lt_one (inv_pos.mpr hcoef))
  have hshort : (128 * A * L) * d ≤ 1 := by
    calc
      _ ≤ (128 * A * L) * (128 * A * L)⁻¹ :=
        mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hcoef.le
      _ = 1 := mul_inv_cancel₀ hcoef.ne'
  exact ⟨L, d, hL, le_max_right _ _, hd, min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), by nlinarith only [hshort]⟩



theorem source_initial_search_anchor_bounds
    {m M d H age : ℝ} (hm : 0 < m) (hd : 0 < d) (hdm : d ≤ m) (hdOne : d ≤ 1)
    (hmH : m ≤ H) (hHM : H ≤ M) (hage : age ∈ Icc (0 : ℝ) 1) :
    let u := -1 + d / (4 * H)
    let shift := -age + H * u
    u ∈ Ioo (-1 : ℝ) 0 ∧ u ≤ -3 / 4 ∧ shift < 0 ∧
      -(M + 3) ≤ shift - 2 * d ∧
      ∀ a : ℝ, a < -d → u + a / H < -1 - 3 * d / (4 * M) := by
  dsimp only
  have hH : 0 < H := hm.trans_le hmH
  have hM : 0 < M := hH.trans_le hHM
  have hdH : d ≤ H := hdm.trans hmH
  have hpos : 0 < d / (4 * H) := div_pos hd (by positivity)
  have hquarter : d / (4 * H) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * H)).mpr
    linarith only [hdH]
  have heq : H * (-1 + d / (4 * H)) = -H + d / 4 := by
    field_simp [hH.ne']
  refine ⟨⟨by linarith only [hpos], by linarith only [hquarter]⟩,
    by linarith only [hquarter], ?_, ?_, ?_⟩
  · rw [heq]
    linarith only [hage.1, hdH, hH]
  · rw [heq]
    linarith only [hage.2, hHM, hdOne]
  · intro a ha
    have hraw : -1 + d / (4 * H) + a / H < -1 - 3 * d / (4 * H) := by
      have hdiv := (div_lt_div_iff_of_pos_right hH).mpr ha
      have hsum : -1 + d / (4 * H) + (-d) / H = -1 - 3 * d / (4 * H) := by
        field_simp [hH.ne']
        ring
      rw [← hsum]
      linarith only [hdiv]
    have hratio : 3 * d / (4 * M) ≤ 3 * d / (4 * H) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hHM])
    exact hraw.trans_le (sub_le_sub_left hratio _)



theorem source_initial_search_physical_clock
    {base birth Q q u : ℝ} (hQ : 0 < Q) (hq : 0 < q) :
    base + (-(Q * (base - birth)) + (Q / q) * u) / Q = birth + u / q := by
  field_simp [hQ.ne', hq.ne']
  ring

end PoincareConjecture.M47
