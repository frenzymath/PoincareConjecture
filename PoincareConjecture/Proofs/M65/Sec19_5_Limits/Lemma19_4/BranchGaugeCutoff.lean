import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeTransform
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]





theorem exists_small_compact_coefficient {A : ℂ → B} {s : Set ℂ}
    (hs : IsOpen s) (h0 : (0 : ℂ) ∈ s) (hA : ContDiffOn ℝ 1 A s) :
    ∃ (A0 : ℂ → B) (R B0 B1 δ : ℝ),
      0 < R ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧ 0 < δ ∧
      ContDiff ℝ 1 A0 ∧ tsupport A0 ⊆ closedBall (0 : ℂ) R ∧
      (∀ z, ‖A0 z‖ ≤ B0) ∧ (∀ z, ‖fderiv ℝ A0 z‖ ≤ B1) ∧
      8 * R * (B0 + δ * B1) < 1 / 2 ∧ A0 =ᶠ[𝓝 0] A := by
  let B0 := ‖A 0‖ + 1
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hc : ContinuousAt A 0 := (hA.contDiffAt (hs.mem_nhds h0)).continuousAt
  have hnb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖A z‖ < B0 :=
    hc.norm.eventually (gt_mem_nhds (by dsimp only [B0]; linarith))
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hs.mem_nhds h0) hnb)
  obtain ⟨rho, hrho, hrhoSmall⟩ := exists_pos_mul_lt
    (by norm_num : (0 : ℝ) < 1 / 4) (8 * B0)
  obtain ⟨R, hR, hRlt⟩ := exists_between (lt_min hr hrho)
  have hRsmall : 8 * R * B0 < 1 / 4 := by
    calc
      _ = (8 * B0) * R := by ring
      _ ≤ (8 * B0) * rho :=
        mul_le_mul_of_nonneg_left (lt_of_lt_of_le hRlt (min_le_right _ _)).le (by positivity)
      _ < _ := hrhoSmall
  let θ : ContDiffBump (0 : ℂ) :=
    { rIn := R / 2, rOut := R, rIn_pos := half_pos hR, rIn_lt_rOut := half_lt_self hR }
  let A0 := fun z => θ z • A z
  have hθsupport : tsupport θ = closedBall (0 : ℂ) R := θ.tsupport_eq
  have hball (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) : z ∈ s ∧ ‖A z‖ < B0 :=
    hrs (closedBall_subset_ball (lt_of_lt_of_le hRlt (min_le_left _ _)) hz)
  have hA0 : ContDiff ℝ 1 A0 := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport θ
    · have hzs := (hball z (hθsupport ▸ hz)).1
      exact θ.contDiff.contDiffAt.smul (hA.contDiffAt (hs.mem_nhds hzs))
    · have hzero := notMem_tsupport_iff_eventuallyEq.mp hz
      apply (contDiffAt_const (c := (0 : B))).congr_of_eventuallyEq
      filter_upwards [hzero] with w hw
      change θ w • A w = (0 : B)
      rw [hw, Pi.zero_apply, zero_smul]
  have hsupport : tsupport A0 ⊆ closedBall (0 : ℂ) R :=
    (tsupport_smul_subset_left θ A).trans hθsupport.subset
  have hcompact : HasCompactSupport A0 :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hsupport
  have hvalue (z : ℂ) : ‖A0 z‖ ≤ B0 := by
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · change ‖θ z • A z‖ ≤ B0
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg θ.nonneg]
      exact (mul_le_mul θ.le_one (hball z hz).2.le (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    · have hzero : A0 z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsupport h))
      simpa only [hzero, norm_zero] using hB0.le
  obtain ⟨D, hD⟩ := (hcompact.fderiv ℝ).exists_bound_of_continuous
    (hA0.continuous_fderiv one_ne_zero)
  let B1 := max D 0
  have hB1 : 0 ≤ B1 := le_max_right _ _
  have hderiv (z : ℂ) : ‖fderiv ℝ A0 z‖ ≤ B1 := (hD z).trans (le_max_left _ _)
  obtain ⟨δ, hδ, hδsmall⟩ := exists_pos_mul_lt
    (by norm_num : (0 : ℝ) < 1 / 4) (8 * R * B1)
  refine ⟨A0, R, B0, B1, δ, hR, hB0.le, hB1, hδ, hA0, hsupport, hvalue, hderiv, ?_, ?_⟩
  · nlinarith only [hRsmall, hδsmall]
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hR)] with z hz
    change θ z • A z = A z
    rw [θ.one_of_mem_closedBall (ball_subset_closedBall hz), one_smul]

end PoincareConjecture.M65Branch
