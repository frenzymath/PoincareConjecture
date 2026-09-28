import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryThinStrip

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

theorem m64NormalCutoff_fderiv_eq_zero_of_lt_one (n : ℕ) (p : LoopPlane)
    (hp : ((n : ℝ) + 1) * p 0 < 1) :
    fderiv ℝ (normalCutoff n) p = 0 := by
  have he : normalCutoff n =ᶠ[𝓝 p] fun _ : LoopPlane => (0 : ℝ) := by
    have ho : IsOpen {q : LoopPlane | ((n : ℝ) + 1) * q 0 < 1} :=
      isOpen_lt (continuous_const.mul
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous) continuous_const
    filter_upwards [ho.mem_nhds hp] with q hq
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  simpa using he.fderiv_eq

theorem m64NormalCutoff_uniform_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (p : LoopPlane),
      ‖fderiv ℝ (normalCutoff n) p (EuclideanSpace.single 0 1)‖ ≤ C * ((n : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_normalCutoff_normal_bound (d := 2)
  refine ⟨C, hC, ?_⟩
  intro n p
  have hn : 0 < (n : ℝ) + 1 := by positivity
  by_cases hp : 1 ≤ ((n : ℝ) + 1) * p 0
  · have hp0 : 0 ≤ p 0 := by nlinarith
    have hb := mul_le_mul_of_nonneg_left (hbound n p hp0) hn.le
    have hl := mul_le_mul_of_nonneg_right hp
      (norm_nonneg (fderiv ℝ (normalCutoff n) p (EuclideanSpace.single 0 1)))
    nlinarith
  · rw [m64NormalCutoff_fderiv_eq_zero_of_lt_one n p (lt_of_not_ge hp)]
    simpa using mul_nonneg hC hn.le

theorem m64NormalCutoff_zeroTrace_support {u : LoopPlane → ℝ} {R : ℝ}
    (hs : tsupport u ⊆ ball 0 R) (n : ℕ) :
    support (fun p => u p * fderiv ℝ (normalCutoff n) p
      (EuclideanSpace.single 0 1)) ⊆
        m64BoundaryThinStrip R (2 / ((n : ℝ) + 1)) := by
  intro p hp
  have hu : u p ≠ 0 := (mul_ne_zero_iff.mp hp).1
  have hd : fderiv ℝ (normalCutoff n) p (EuclideanSpace.single 0 1) ≠ 0 :=
    (mul_ne_zero_iff.mp hp).2
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hl : 1 ≤ ((n : ℝ) + 1) * p 0 := by
    by_contra! hh
    exact hd (by rw [m64NormalCutoff_fderiv_eq_zero_of_lt_one n p hh]; rfl)
  have hh : ((n : ℝ) + 1) * p 0 ≤ 2 := by
    by_contra! hh
    exact hd (by rw [normalCutoff_fderiv_eq_zero_of_two_lt n p hh]; rfl)
  have hball := hs (subset_tsupport u hu)
  have hnorm : ‖p‖ < R := by simpa only [mem_ball, dist_zero_right] using hball
  have hcoord : |p 1| < R := (PiLp.norm_apply_le p 1).trans_lt hnorm
  refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
  · exact (le_div_iff₀ hn).mpr (by linarith)
  · exact ⟨(abs_lt.mp hcoord).1.le, (abs_lt.mp hcoord).2.le⟩

theorem m64NormalCutoff_zeroTrace_error_tendsto {u : LoopPlane → ℝ}
    (hu : Continuous u) (hc : HasCompactSupport u)
    (hzero : ∀ p : LoopPlane, p 0 = 0 → u p = 0) :
    Tendsto (fun n => ∫ p in halfSpace 2,
      u p * fderiv ℝ (normalCutoff n) p (EuclideanSpace.single 0 1)) atTop (𝓝 0) := by
  obtain ⟨R, hR, hs⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0 : LoopPlane)
  obtain ⟨C, hC, hbound⟩ := m64NormalCutoff_uniform_derivative_bound
  apply Metric.tendsto_atTop.mpr
  intro epsilon he
  let eta := epsilon / (4 * R * C + 1)
  have hden : 0 < 4 * R * C + 1 := by positivity
  have heta : 0 < eta := div_pos he hden
  obtain ⟨delta, hd, hsmall⟩ := m64Continuous_zero_trace_uniform_small hu hc hzero heta
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / delta)
  refine ⟨N, ?_⟩
  intro n hn
  have hn0 : 0 < (n : ℝ) + 1 := by positivity
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hwidth : 2 / ((n : ℝ) + 1) < delta := by
    apply (div_lt_iff₀ hn0).mpr
    have hh := (div_lt_iff₀ hd).mp hN
    nlinarith
  let f : LoopPlane → ℝ := fun p =>
    u p * fderiv ℝ (normalCutoff n) p (EuclideanSpace.single 0 1)
  let S := m64BoundaryThinStrip R (2 / ((n : ℝ) + 1))
  have hfs : support f ⊆ S := m64NormalCutoff_zeroTrace_support hs n
  have hfh : support f ⊆ halfSpace 2 := by
    intro p hp
    have hd' := (mul_ne_zero_iff.mp hp).2
    by_contra hp'
    have hp0 : p 0 ≤ 0 := le_of_not_gt hp'
    have hz := m64NormalCutoff_fderiv_eq_zero_of_lt_one n p
      (show ((n : ℝ) + 1) * p 0 < 1 by nlinarith)
    exact hd' (by rw [hz]; rfl)
  have hiH : (∫ p in halfSpace 2, f p) = ∫ p, f p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by
      by_contra hf
      exact hp (hfh hf)
  have hiS : (∫ p in S, f p) = ∫ p, f p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by
      by_contra hf
      exact hp (hfs hf)
  have hestimate : ‖∫ p in S, f p‖ ≤ eta * C * ((n : ℝ) + 1) * volume.real S := by
    apply norm_setIntegral_le_of_norm_le_const
      (lt_top_iff_ne_top.mpr (m64BoundaryThinStrip_volume_ne_top _ _))
    intro p hp
    have hps : |p 0| < delta := by
      rw [abs_of_nonneg hp.1.1]
      exact hp.1.2.trans_lt hwidth
    dsimp only [f]
    rw [norm_mul]
    calc
      _ ≤ eta * (C * ((n : ℝ) + 1)) :=
        mul_le_mul (hsmall p hps).le (hbound n p) (norm_nonneg _) heta.le
      _ = _ := by ring
  have hv : volume.real S = 2 * R * (2 / ((n : ℝ) + 1)) :=
    m64BoundaryThinStrip_volume_real hR.le (by positivity)
  change dist (∫ p in halfSpace 2, f p) 0 < epsilon
  rw [dist_zero_right, hiH, ← hiS]
  apply hestimate.trans_lt
  rw [hv]
  have heq : eta * C * ((n : ℝ) + 1) * (2 * R * (2 / ((n : ℝ) + 1))) =
      eta * (4 * R * C) := by field_simp; ring
  rw [heq]
  have heq' : eta * (4 * R * C + 1) = epsilon := div_mul_cancel₀ epsilon hden.ne'
  nlinarith

end PoincareConjecture
