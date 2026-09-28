import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeTerms
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

def cauchyGauge (A : ℂ → B) (z : ℂ) : B := ∑' n, cauchyTerm A n z

theorem cauchyGauge_spec [CompleteSpace B] [NormOneClass B]
    {A : ℂ → B} {R B0 B1 δ : ℝ}
    (hR : 0 < R) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hδ : 0 < δ)
    (hA : ContDiff ℝ 1 A) (hsupport : tsupport A ⊆ closedBall (0 : ℂ) R)
    (hvalue : ∀ z, ‖A z‖ ≤ B0) (hderiv : ∀ z, ‖fderiv ℝ A z‖ ≤ B1)
    (hsmall : 8 * R * (B0 + δ * B1) < 1 / 2) :
    ContDiff ℝ 1 (cauchyGauge A) ∧
      (∀ z, dbar (cauchyGauge A) z = A z * cauchyGauge A z) ∧
      (∀ z, ‖cauchyGauge A z - 1‖ < 1) ∧
      (∀ z, IsUnit (cauchyGauge A z)) := by
  let q := 8 * R * (B0 + δ * B1)
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hqhalf : q < 1 / 2 := hsmall
  have hq1 : q < 1 := lt_trans hqhalf (by norm_num)
  have hs : HasCompactSupport A :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hsupport
  have hT (n : ℕ) := contDiff_cauchyTerm hA hs n
  have hbound (n : ℕ) (z : ℂ) :
      ‖cauchyTerm A n z‖ ≤ q ^ n ∧ ‖fderiv ℝ (cauchyTerm A n) z‖ ≤ δ⁻¹ * q ^ n :=
    cauchyTerm_bounds hR hB0 hB1 hδ hA hsupport hvalue hderiv n z
  have hgeom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hgeomD : Summable (fun n : ℕ => δ⁻¹ * q ^ n) := Summable.mul_left _ hgeom
  have hsum (z : ℂ) : Summable (fun n => cauchyTerm A n z) :=
    hgeom.of_norm_bounded (fun n => (hbound n z).1)
  have hsumD (z : ℂ) : Summable (fun n => fderiv ℝ (cauchyTerm A n) z) :=
    hgeomD.of_norm_bounded (fun n => (hbound n z).2)
  have hD (z : ℂ) : HasFDerivAt (cauchyGauge A)
      (∑' n, fderiv ℝ (cauchyTerm A n) z) z :=
    hasFDerivAt_tsum hgeomD
      (fun n w => ((hT n).differentiable one_ne_zero w).hasFDerivAt)
      (fun n w => (hbound n w).2) (hsum 0) z
  have hC1 : ContDiff ℝ 1 (cauchyGauge A) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨_,
      continuous_tsum (fun n => (hT n).continuous_fderiv one_ne_zero)
        hgeomD (fun n w => (hbound n w).2), hD⟩
  have heq (z : ℂ) : dbar (cauchyGauge A) z = A z * cauchyGauge A z := by
    have hsumbar : Summable (fun n => dbar (cauchyTerm A n) z) :=
      (dbarLinear.hasSum (hsumD z).hasSum).summable
    have hzero : dbar (cauchyTerm A 0) z = 0 := by
      change dbarLinear (fderiv ℝ (fun _ : ℂ => (1 : B)) z) = 0
      rw [(hasFDerivAt_const (𝕜 := ℝ) (1 : B) z).fderiv, map_zero]
    change dbarLinear (fderiv ℝ (cauchyGauge A) z) = _
    rw [(hD z).fderiv, dbarLinear.map_tsum (hsumD z)]
    change (∑' n, dbar (cauchyTerm A n) z) = _
    rw [hsumbar.tsum_eq_zero_add]
    simp only [hzero, dbar_cauchyTerm_succ hA hs, zero_add]
    exact Summable.tsum_mul_left (A z) (hsum z)
  have hclose (z : ℂ) : ‖cauchyGauge A z - 1‖ < 1 := by
    have htail : cauchyGauge A z - 1 = ∑' n, cauchyTerm A (n + 1) z := by
      rw [cauchyGauge, (hsum z).tsum_eq_zero_add]
      change (1 : B) + (∑' n, cauchyTerm A (n + 1) z) - 1 = _
      abel
    have hsucc : HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
      simpa only [pow_succ', div_eq_mul_inv] using
        HasSum.mul_left q (hasSum_geometric_of_lt_one hq0 hq1)
    have hle : ‖cauchyGauge A z - 1‖ ≤ q / (1 - q) := by
      rw [htail]
      exact tsum_of_norm_bounded hsucc (fun n => (hbound (n + 1) z).1)
    exact hle.trans_lt ((div_lt_one (sub_pos.mpr hq1)).mpr (by linarith))
  refine ⟨hC1, heq, hclose, ?_⟩
  intro z
  have hrev : ‖1 - cauchyGauge A z‖ < 1 := by rw [norm_sub_rev]; exact hclose z
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hrev

end PoincareConjecture.M65Branch
