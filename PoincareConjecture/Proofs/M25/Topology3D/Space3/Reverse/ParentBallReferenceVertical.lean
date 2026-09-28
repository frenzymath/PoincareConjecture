import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmallPerturbation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology NNReal

namespace PoincareConjecture.M25.Topology3D

private theorem reference_vertical_primitive_smooth (κ : ℝ) (b : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun z => κ * z + (1 - κ) * ∫ s in 0..z, b s) ∧
      ∀ z, HasDerivAt (fun z => κ * z + (1 - κ) * ∫ s in 0..z, b s)
        (κ + (1 - κ) * b z) z := by
  have hd (z : ℝ) :
      HasDerivAt (fun z => κ * z + (1 - κ) * ∫ s in 0..z, b s)
        (κ + (1 - κ) * b z) z := by
    have hi : HasDerivAt (fun y : ℝ => ∫ s in 0..y, b s) (b z) z :=
      intervalIntegral.integral_hasDerivAt_right
        (hb.continuous.intervalIntegrable 0 z)
        hb.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hb.continuous.continuousAt
    simpa only [mul_one] using!
      ((hasDerivAt_id z).const_mul κ).add (hi.const_mul (1 - κ))
  refine ⟨contDiff_infty_iff_deriv.mpr ⟨fun z => (hd z).differentiableAt, ?_⟩, hd⟩
  have heq :
      deriv (fun z => κ * z + (1 - κ) * ∫ s in 0..z, b s) =
        fun z => κ + (1 - κ) * b z := funext fun z => (hd z).deriv
  rw [heq]
  exact contDiff_const.add (contDiff_const.mul hb)

private theorem reference_vertical_cutoff_integral_le (τ : ℝ) (hτ : 0 < τ)
    (b : ℝ → ℝ) (hb : Continuous b) (hb1 : ∀ s, b s ≤ 1)
    (hbzero : ∀ s, s ≤ -τ → b s = 0) (z : ℝ) (hz : z ≤ 0) :
    (∫ s in z..0, b s) ≤ τ := by
  have hbound (a : ℝ) (ha : a ≤ 0) : (∫ s in a..0, b s) ≤ -a := by
    have h := intervalIntegral.integral_mono_on (μ := volume) ha (hb.intervalIntegrable a 0)
      (continuous_const.intervalIntegrable a 0) (fun s _ => hb1 s)
    simpa only [intervalIntegral.integral_const, sub_zero, zero_sub, smul_eq_mul,
      mul_one] using h
  by_cases hzt : -τ ≤ z
  · exact (hbound z hz).trans (by linarith only [hzt])
  · have hzt' : z ≤ -τ := (lt_of_not_ge hzt).le
    have hzero : (∫ s in z..(-τ), b s) = 0 := by
      calc
        (∫ s in z..(-τ), b s) = ∫ s in z..(-τ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hzt'] at hs
          exact hbzero s hs.2
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hb.intervalIntegrable z (-τ)) (hb.intervalIntegrable (-τ) 0)
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    simpa only [neg_neg] using hbound (-τ) (by linarith only [hτ])





theorem exists_reference_vertical_diffeomorph (L η : ℝ) (hL : 1 ≤ L) (hη : 0 < η) :
    ∃ f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      f 0 = 0 ∧ StrictMono f ∧
        (∀ z : ℝ, |z| ≤ η / 8 → f z = z) ∧
        ∀ z : ℝ, z ∈ Icc (-L) 0 → f z ∈ Ioc (-η) 0 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let τ : ℝ := η / 4
  let κ : ℝ := min (1 / 2) (η / (4 * L))
  have hτ : 0 < τ := div_pos hη (by norm_num)
  have hκ : 0 < κ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hκhalf : κ ≤ 1 / 2 := min_le_left _ _
  have hκone : κ < 1 := by linarith only [hκhalf]
  have hκL : κ * L ≤ τ := by
    have hmul := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ)
      (η / (4 * L))) hLpos.le
    have heq : η / (4 * L) * L = τ := by
      dsimp only [τ]
      field_simp
    exact hmul.trans_eq heq
  have hcut : Icc (-τ / 2) (τ / 2) ⊆ Ioo (-τ) τ := by
    intro s hs
    exact ⟨by linarith only [hs.1, hτ], by linarith only [hs.2, hτ]⟩
  obtain ⟨b, hb, _, hbs, hbnear, hbrange⟩ :=
    exists_compact_smooth_cutoff isCompact_Icc isOpen_Ioo hcut
  have hbone (s : ℝ) (hs : s ∈ Icc (-τ / 2) (τ / 2)) : b s = 1 :=
    subset_of_mem_nhdsSet hbnear hs
  have hbzero (s : ℝ) (hs : s ≤ -τ) : b s = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (not_lt_of_ge hs) (hbs hmem).1
  let F : ℝ → ℝ := fun z => κ * z + (1 - κ) * ∫ s in 0..z, b s
  obtain ⟨hF, hdF⟩ := reference_vertical_primitive_smooth κ b hb
  have hderiv (z : ℝ) : deriv F z = κ + (1 - κ) * b z := (hdF z).deriv
  have hmono : StrictMono F := by
    apply strictMono_of_deriv_pos
    intro z
    rw [hderiv]
    exact add_pos_of_pos_of_nonneg hκ
      (mul_nonneg (sub_nonneg.mpr hκone.le) (hbrange z).1)
  let g : ℝ → ℝ := fun z => F z - z
  have hg : ContDiff ℝ ∞ g := hF.sub contDiff_id
  let C : ℝ≥0 := ⟨1 - κ, sub_nonneg.mpr hκone.le⟩
  have hC : C < 1 := by
    change 1 - κ < (1 : ℝ)
    linarith only [hκ]
  have hglip : LipschitzWith C g := by
    apply lipschitzWith_of_nnnorm_deriv_le (hg.differentiable (by simp))
    intro z
    have hdg : HasDerivAt g (κ + (1 - κ) * b z - 1) z :=
      (hdF z).sub (hasDerivAt_id z)
    apply NNReal.coe_le_coe.mp
    change ‖deriv g z‖ ≤ 1 - κ
    rw [hdg.deriv, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have hnonneg := mul_nonneg (sub_nonneg.mpr hκone.le) (hbrange z).1
      linarith only [hnonneg]
    · have hupper := mul_le_mul_of_nonneg_left (hbrange z).2
        (sub_nonneg.mpr hκone.le)
      linarith only [hupper, hκone]
  let f := smallPerturbationDiffeomorph g hg hC hglip
  have hf (z : ℝ) : f z = F z := by
    change z + (F z - z) = F z
    ring
  have hFzero : F 0 = 0 := by simp only [F, intervalIntegral.integral_same,
    mul_zero, add_zero]
  refine ⟨f, (hf 0).trans hFzero, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [hf, hf]
    exact hmono hxy
  · intro z hz
    have hz' : z ∈ Icc (-τ / 2) (τ / 2) := by
      obtain ⟨hl, hu⟩ := abs_le.mp hz
      constructor <;> dsimp only [τ] <;> linarith only [hl, hu]
    have hzero : (0 : ℝ) ∈ Icc (-τ / 2) (τ / 2) := by
      constructor <;> linarith only [hτ]
    have hi : (∫ s in 0..z, b s) = z := by
      calc
        (∫ s in 0..z, b s) = ∫ s in 0..z, (1 : ℝ) :=
          intervalIntegral.integral_congr
            (fun s hs => hbone s (uIcc_subset_Icc hzero hz' hs))
        _ = z := by simp
    rw [hf]
    dsimp only [F]
    rw [hi]
    ring
  · intro z hz
    have hi0 : 0 ≤ ∫ s in z..0, b s :=
      intervalIntegral.integral_nonneg_of_forall hz.2 (fun s => (hbrange s).1)
    have hiτ : (∫ s in z..0, b s) ≤ τ :=
      reference_vertical_cutoff_integral_le τ hτ b hb.continuous
        (fun s => (hbrange s).2) hbzero z hz.2
    have hprod : (1 - κ) * (∫ s in z..0, b s) ≤ τ := by
      calc
        (1 - κ) * (∫ s in z..0, b s) ≤ 1 * (∫ s in z..0, b s) :=
          mul_le_mul_of_nonneg_right (by linarith only [hκ]) hi0
        _ ≤ τ := by simpa only [one_mul] using hiτ
    have hlinear : -(κ * L) ≤ κ * z := by
      have hmul := mul_le_mul_of_nonneg_left hz.1 hκ.le
      simpa only [mul_neg] using hmul
    have hFbound : -η < F z := by
      dsimp only [F]
      rw [intervalIntegral.integral_symm z 0]
      have hηhalf : -(η / 2) < 0 := by linarith only [hη]
      dsimp only [τ] at hκL hprod
      nlinarith only [hlinear, hκL, hprod, hηhalf]
    refine ⟨by rw [hf]; exact hFbound, ?_⟩
    rw [hf, ← hFzero]
    exact hmono.monotone hz.2

end PoincareConjecture.M25.Topology3D
