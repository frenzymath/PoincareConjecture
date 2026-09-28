import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

def normBoundEntropy (C s : ℝ) : ℝ :=
  ∫ u in C..s, Real.smoothTransition (u - C)

theorem normBoundEntropy_hasDerivAt (C s : ℝ) :
    HasDerivAt (normBoundEntropy C) (Real.smoothTransition (s - C)) s := by
  have hc : Continuous (fun u : ℝ => Real.smoothTransition (u - C)) :=
    Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable C s)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem normBoundEntropy_deriv (C : ℝ) :
    deriv (normBoundEntropy C) = fun s => Real.smoothTransition (s - C) :=
  funext fun s => (normBoundEntropy_hasDerivAt C s).deriv

theorem normBoundEntropy_contDiff (C : ℝ) : ContDiff ℝ ∞ (normBoundEntropy C) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (normBoundEntropy_hasDerivAt C s).differentiableAt, ?_⟩
  rw [normBoundEntropy_deriv]
  exact Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem normBoundEntropy_zero_of_le {C s : ℝ} (hs : s ≤ C) : normBoundEntropy C s = 0 := by
  unfold normBoundEntropy
  rw [intervalIntegral.integral_symm]
  have hz : (∫ u in s..C, Real.smoothTransition (u - C)) = ∫ _u in s..C, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs] at hu
    exact Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hu.2)
  rw [hz]
  simp

theorem normBoundEntropy_pos {C s : ℝ} (hs : C < s) : 0 < normBoundEntropy C s := by
  have hc : Continuous (fun u : ℝ => Real.smoothTransition (u - C)) :=
    Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable C s)
    (fun u hu => Real.smoothTransition.pos_of_pos (sub_pos.mpr hu.1)) hs

theorem normBoundEntropy_nonneg (C s : ℝ) : 0 ≤ normBoundEntropy C s := by
  by_cases hs : s ≤ C
  · rw [normBoundEntropy_zero_of_le hs]
  · exact (normBoundEntropy_pos (lt_of_not_ge hs)).le

theorem normBoundEntropy_eq_zero_iff (C s : ℝ) : normBoundEntropy C s = 0 ↔ s ≤ C := by
  constructor
  · intro h
    by_contra hs
    exact (normBoundEntropy_pos (lt_of_not_ge hs)).ne' h
  · exact normBoundEntropy_zero_of_le

theorem normBoundEntropy_deriv_nonneg (C s : ℝ) : 0 ≤ deriv (normBoundEntropy C) s := by
  rw [normBoundEntropy_deriv]
  exact Real.smoothTransition.nonneg _

theorem normBoundEntropy_deriv_le_one (C s : ℝ) : deriv (normBoundEntropy C) s ≤ 1 := by
  rw [normBoundEntropy_deriv]
  exact Real.smoothTransition.le_one _

theorem normBoundEntropy_second_nonneg (C s : ℝ) :
    0 ≤ deriv (deriv (normBoundEntropy C)) s := by
  rw [normBoundEntropy_deriv]
  apply Monotone.deriv_nonneg
  intro a b hab
  exact Real.smoothTransition.monotone (sub_le_sub_right hab C)

theorem normBoundEntropy_second_zero {C s : ℝ} (hs : s ∉ Icc C (C + 1)) :
    deriv (deriv (normBoundEntropy C)) s = 0 := by
  rw [normBoundEntropy_deriv]
  rcases lt_or_ge s C with hlt | hge
  · have he : (fun u => Real.smoothTransition (u - C)) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with u hu
      exact Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hu.le)
    rw [he.deriv_eq]
    simp
  · have hgt : C + 1 < s := lt_of_not_ge fun h => hs ⟨hge, h⟩
    have he : (fun u => Real.smoothTransition (u - C)) =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hgt] with u hu
      apply Real.smoothTransition.one_of_one_le
      have hCu : C + 1 < u := hu
      linarith
    rw [he.deriv_eq]
    simp

theorem normBoundEntropy_second_hasCompactSupport (C : ℝ) :
    HasCompactSupport (deriv (deriv (normBoundEntropy C))) := by
  apply (isCompact_Icc : IsCompact (Icc C (C + 1))).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_Icc
  intro s hs
  by_contra hn
  exact hs (normBoundEntropy_second_zero hn)


theorem normBoundEntropy_le {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s) :
    normBoundEntropy C s ≤ s := by
  by_cases h : s ≤ C
  · simpa [normBoundEntropy_zero_of_le h] using hs
  · have hCs := le_of_lt (lt_of_not_ge h)
    have hc : Continuous (fun u : ℝ => Real.smoothTransition (u - C)) :=
      Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)
    have hb := intervalIntegral.integral_mono_on hCs (hc.intervalIntegrable C s)
      (continuous_const.intervalIntegrable C s :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume C s)
      (fun u _ => Real.smoothTransition.le_one (u - C))
    have hlast : (∫ _u in C..s, (1 : ℝ)) ≤ s := by simp; linarith
    exact hb.trans hlast

end PoincareConjecture.M35.Uniqueness.Heat
