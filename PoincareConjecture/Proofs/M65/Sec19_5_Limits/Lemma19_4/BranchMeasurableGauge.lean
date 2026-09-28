import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyContinuity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65Branch

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
  [CompleteSpace B] [NormOneClass B]

theorem cauchyTerm_continuous_bound {A : ℂ → B} {R B0 : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (n : ℕ) :
    Continuous (cauchyTerm A n) ∧
      ∀ z, ‖cauchyTerm A n z‖ ≤ (8 * R * B0) ^ n := by
  let q := 8 * R * B0
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  change Continuous (cauchyTerm A n) ∧ ∀ z, ‖cauchyTerm A n z‖ ≤ q ^ n
  induction n with
  | zero =>
    exact ⟨continuous_const, fun _ => by simp only [cauchyTerm, norm_one, pow_zero, le_refl]⟩
  | succ n ih =>
    have hp : AEStronglyMeasurable (fun z => A z * cauchyTerm A n z) volume :=
      hA.mul ih.1.aestronglyMeasurable
    have hps : Function.support (fun z => A z * cauchyTerm A n z) ⊆
        closedBall (0 : ℂ) R := (Function.support_mul_subset_left _ _).trans hs
    have hpb (z : ℂ) : ‖A z * cauchyTerm A n z‖ ≤ B0 * q ^ n :=
      (norm_mul_le _ _).trans (mul_le_mul (hb z) (ih.2 z) (norm_nonneg _) hB)
    refine ⟨continuous_cauchyOperator_of_bound (by positivity) hp hps hpb, ?_⟩
    intro z
    exact (norm_cauchyOperator_le_of_bound hR (by positivity) hp hps hpb z).trans_eq
      (by dsimp only [q]; rw [pow_succ]; ring)

theorem cauchyGauge_measurable_spec {A : ℂ → B} {R B0 : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2) :
    Continuous (cauchyGauge A) ∧
      (∀ z, cauchyGauge A z = 1 + cauchyOperator (fun w => A w * cauchyGauge A w) z) ∧
      (∀ z, ‖cauchyGauge A z - 1‖ < 1) ∧
      (∀ z, IsUnit (cauchyGauge A z)) := by
  let q := 8 * R * B0
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hqhalf : q < 1 / 2 := hsmall
  have hq1 : q < 1 := lt_trans hqhalf (by norm_num)
  have hT (n : ℕ) : Continuous (cauchyTerm A n) ∧
      ∀ z, ‖cauchyTerm A n z‖ ≤ q ^ n :=
    cauchyTerm_continuous_bound hR hB hA hs hb n
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  have hsum (z : ℂ) : Summable (fun n => cauchyTerm A n z) :=
    hgeom.of_norm_bounded (fun n => (hT n).2 z)
  have hcont : Continuous (cauchyGauge A) :=
    continuous_tsum (fun n => (hT n).1) hgeom (fun n z => (hT n).2 z)
  have heq (z : ℂ) : cauchyGauge A z =
      1 + cauchyOperator (fun w => A w * cauchyGauge A w) z := by
    let F (n : ℕ) (w : ℂ) := (z - w)⁻¹ • (A w * cauchyTerm A n w)
    have hFi (n : ℕ) : Integrable (F n) :=
      integrable_cauchyOperator_of_bound (hA.mul (hT n).1.aestronglyMeasurable)
        ((Function.support_mul_subset_left _ _).trans hs)
        (fun w => (norm_mul_le _ _).trans
          (mul_le_mul (hb w) ((hT n).2 w) (norm_nonneg _) hB)) z
    have hk := integrable_cauchyOperator_of_bound hA hs hb z
    have hFb (n : ℕ) (w : ℂ) :
        ‖F n w‖ ≤ ‖(z - w)⁻¹ • A w‖ * q ^ n := by
      dsimp only [F]
      rw [← smul_mul_assoc]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ((hT n).2 w) (norm_nonneg _))
    have hIsum : Summable (fun n => ∫ w : ℂ, ‖F n w‖) := by
      apply (hgeom.mul_left (∫ w : ℂ, ‖(z - w)⁻¹ • A w‖)).of_norm_bounded
      intro n
      rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg (F n w))]
      calc
        _ ≤ ∫ w : ℂ, ‖(z - w)⁻¹ • A w‖ * q ^ n :=
          integral_mono_ae (hFi n).norm (hk.norm.mul_const _) (ae_of_all _ (hFb n))
        _ = _ := integral_mul_const _ _
    have hsumint : Summable (fun n => ∫ w : ℂ, F n w) :=
      (hasSum_integral_of_summable_integral_norm hFi hIsum).summable
    have hpoint (w : ℂ) : (∑' n, F n w) =
        (z - w)⁻¹ • (A w * cauchyGauge A w) :=
      (((hsum w).hasSum.mul_left (A w)).const_smul (z - w)⁻¹).tsum_eq
    have hC : cauchyOperator (fun w => A w * cauchyGauge A w) z =
        ∑' n, cauchyTerm A (n + 1) z := by
      calc
        _ = (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, ∑' n, F n w := by
          rw [cauchyOperator]
          congr 1
          exact integral_congr_ae (ae_of_all _ fun w => (hpoint w).symm)
        _ = (Real.pi : ℂ)⁻¹ • ∑' n, ∫ w : ℂ, F n w := by
          rw [integral_tsum_of_summable_integral_norm hFi hIsum]
        _ = ∑' n, (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, F n w :=
          (hsumint.tsum_const_smul _).symm
        _ = _ := rfl
    rw [hC, cauchyGauge, (hsum z).tsum_eq_zero_add]
    rfl
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
      exact tsum_of_norm_bounded hsucc (fun n => (hT (n + 1)).2 z)
    exact hle.trans_lt ((div_lt_one (sub_pos.mpr hq1)).mpr (by linarith))
  refine ⟨hcont, heq, hclose, ?_⟩
  intro z
  have hrev : ‖1 - cauchyGauge A z‖ < 1 := by rw [norm_sub_rev]; exact hclose z
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hrev

end PoincareConjecture.M65Branch
