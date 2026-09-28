import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCauchyHolder
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65Gauss

private theorem exists_collar_level {E : ℝ → ℝ} {a delta : ℝ} {Good : ℝ → Prop}
    (hd : 0 < delta) (hda : delta ≤ 1 - a)
    (hE : IntegrableOn E (Ioo a 1))
    (hgood : ∀ᵐ r ∂volume.restrict (Ioo a 1), 0 ≤ E r ∧ Good r) :
    ∃ r ∈ Ioo (1 - delta) (1 - delta / 2),
      0 ≤ E r ∧ Good r ∧
        (1 - r) * E r ≤ 2 * ∫ s in Ioo (1 - delta) (1 - delta / 2), E s := by
  let J := Ioo (1 - delta) (1 - delta / 2)
  let μ := volume.restrict J
  have hsub : J ⊆ Ioo a 1 := fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hμreal : μ.real univ = delta / 2 := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ (1 - delta / 2) - (1 - delta))]
    ring
  have hμ : μ ≠ 0 := by
    intro hz
    have hh : μ.real univ = 0 := by rw [hz]; simp
    rw [hμreal] at hh
    linarith
  have hg : ∀ᵐ r ∂μ, r ∈ J ∧ 0 ≤ E r ∧ Good r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hgood] with r hr hg
    exact ⟨hr, hg⟩
  have hnull : μ {r | ¬(r ∈ J ∧ 0 ≤ E r ∧ Good r)} = 0 := hg
  obtain ⟨r, hr, hle⟩ := exists_notMem_null_le_average (μ := μ)
    (N := {r | ¬(r ∈ J ∧ 0 ≤ E r ∧ Good r)}) hμ (hE.mono_set hsub) hnull
  have hrr : r ∈ J ∧ 0 ≤ E r ∧ Good r := not_not.mp hr
  rw [average_eq, hμreal, smul_eq_mul] at hle
  have hmean : (delta / 2) * E r ≤ ∫ s in J, E s := by
    have hh := mul_le_mul_of_nonneg_left hle (half_pos hd).le
    rwa [← mul_assoc, mul_inv_cancel₀ (half_pos hd).ne', one_mul] at hh
  refine ⟨r, hrr.1, hrr.2.1, hrr.2.2, ?_⟩
  calc
    (1 - r) * E r ≤ delta * E r :=
      mul_le_mul_of_nonneg_right (by linarith [hrr.1.1]) hrr.2.1
    _ = 2 * ((delta / 2) * E r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean (by norm_num)

theorem exists_collar_levels {E : ℝ → ℝ} {a : ℝ} (ha : a < 1)
    (hE : IntegrableOn E (Ioo a 1)) {Good : ℝ → Prop}
    (hgood : ∀ᵐ r ∂volume.restrict (Ioo a 1), 0 ≤ E r ∧ Good r) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Ioo a 1 ∧ 0 ≤ E (r n) ∧ Good (r n)) ∧
      Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun n => (1 - r n) * E (r n)) atTop (𝓝 0) := by
  let delta := fun n : ℕ => ((1 - a) / 2) * (1 / 2 : ℝ) ^ n
  let J := fun n => Ioo (1 - delta n) (1 - delta n / 2)
  have hd (n : ℕ) : 0 < delta n := by dsimp only [delta]; positivity
  have hda (n : ℕ) : delta n ≤ 1 - a := by
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (1 - a) / 2 by linarith)
    dsimp only [delta]
    linarith
  have hdt : Tendsto delta atTop (𝓝 0) := by
    simpa only [delta, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)))
  choose r hr hEn hGn hbound using fun n => exists_collar_level (hd n) (hda n) hE hgood
  have hJsub (n : ℕ) : J n ⊆ Ioo a 1 := by
    intro s hs
    exact ⟨by linarith [hs.1, hda n], by linarith [hs.2, hd n]⟩
  have hvol (n : ℕ) : (volume.restrict (Ioo a 1)) (J n) =
      ENNReal.ofReal (delta n / 2) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr (hJsub n),
      Real.volume_Ioo]
    congr 1
    ring
  have hvlim : Tendsto (fun n => (volume.restrict (Ioo a 1)) (J n)) atTop (𝓝 0) := by
    simp_rw [hvol]
    simpa only [div_zero, zero_div, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hdt.div_const 2)
  have hIt : Tendsto (fun n => ∫ s in J n, E s) atTop (𝓝 0) := by
    have hh := hE.tendsto_setIntegral_nhds_zero hvlim
    simpa only [Measure.restrict_restrict_of_subset (hJsub _)] using hh
  refine ⟨r, fun n => ⟨hJsub n (hr n), hEn n, hGn n⟩, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => 1 - delta n) atTop (𝓝 1) by
        simpa only [sub_zero] using tendsto_const_nhds.sub hdt)
      tendsto_const_nhds
      (fun n => (hr n).1.le) (fun n => (hJsub n (hr n)).2.le)
  · apply squeeze_zero
      (fun n => mul_nonneg (sub_nonneg.mpr (hJsub n (hr n)).2.le) (hEn n)) hbound
    simpa only [mul_zero] using tendsto_const_nhds.mul hIt

end PoincareConjecture.M65Gauss
