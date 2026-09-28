import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture

theorem m64Intrinsic_exists_equal_integral_partition
    {f : ℝ → ℝ} (hf : Continuous f) (hpos : ∀ t, 0 < f t)
    {P : ℝ} (hP : 0 < P) {n : ℕ} (hn : 0 < n) :
    ∃ p : ℕ → ℝ, p 0 = 0 ∧ p n = P ∧
      (∀ k ≤ n, p k ∈ Icc (0 : ℝ) P) ∧
      ∀ k < n, p k < p (k + 1) ∧
        (∫ x in p k..p (k + 1), f x) = (∫ x in (0 : ℝ)..P, f x) / n := by
  let F : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, f x
  have hFderiv (t : ℝ) : HasDerivAt F (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hFderiv t).continuousAt)
  have hFmono : StrictMono F := strictMono_of_deriv_pos
    (fun t => by rw [(hFderiv t).deriv]; exact hpos t)
  have hFzero : F 0 = 0 := intervalIntegral.integral_same
  have hL : 0 < F P := by simpa only [hFzero] using hFmono hP
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hex (k : ℕ) : ∃ t ∈ Icc (0 : ℝ) P,
      F t = ((min k n : ℕ) : ℝ) / n * F P := by
    apply intermediate_value_Icc hP.le hFcont.continuousOn
    constructor
    · rw [hFzero]
      positivity
    · have hquot : ((min k n : ℕ) : ℝ) / n ≤ 1 :=
        (div_le_one hnReal).mpr (by exact_mod_cast Nat.min_le_right k n)
      exact (mul_le_mul_of_nonneg_right hquot hL.le).trans (by simp)
  choose p hp hpF using hex
  have hpk (k : ℕ) (hk : k ≤ n) : F (p k) = (k : ℝ) / n * F P := by
    simpa only [Nat.min_eq_left hk] using hpF k
  have hp0 : p 0 = 0 := hFmono.injective (by
    simpa only [Nat.cast_zero, zero_div, zero_mul, hFzero] using hpk 0 (Nat.zero_le n))
  have hpn : p n = P := hFmono.injective (by
    simpa only [div_self hnReal.ne', one_mul] using hpk n le_rfl)
  refine ⟨p, hp0, hpn, fun k _ => hp k, ?_⟩
  intro k hk
  have hkn : k ≤ n := hk.le
  have hksn : k + 1 ≤ n := Nat.add_one_le_iff.mpr hk
  have hdiff : F (p (k + 1)) - F (p k) = F P / n := by
    rw [hpk k hkn, hpk (k + 1) hksn, Nat.cast_add, Nat.cast_one]
    ring
  have hpstep : p k < p (k + 1) := by
    apply hFmono.lt_iff_lt.mp
    have hq := div_pos hL hnReal
    linarith
  refine ⟨hpstep, ?_⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 (p k)) (hf.intervalIntegrable (p k) (p (k + 1)))
  change F (p k) + (∫ x in p k..p (k + 1), f x) = F (p (k + 1)) at hadd
  change (∫ x in p k..p (k + 1), f x) = F P / n
  linarith

theorem m64Intrinsic_exists_equal_boundary_length_partition
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    ∃ p : ℕ → ℝ, p 0 = 0 ∧ p n = rampPeriod ∧
      (∀ k ≤ n, p k ∈ Icc (0 : ℝ) rampPeriod) ∧
      ∀ k < n, p k < p (k + 1) ∧
        intrinsicBoundaryLength N.metric radius (p k) (p (k + 1)) =
          intrinsicBoundaryLength N.metric radius 0 rampPeriod / n := by
  exact m64Intrinsic_exists_equal_integral_partition
    (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous
    (m64Intrinsic_boundarySpeed_pos N hradius)
    (show 0 < rampPeriod from Real.two_pi_pos) hn

end PoincareConjecture
