import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityKernel











set_option autoImplicit false

open Set Metric MeasureTheory Complex
open scoped Topology

namespace PoincareConjecture.M65Boundary

open M65Branch






theorem weighted_cauchy_estimate {b : ℝ} (hb : 1 < b) (hb2 : b < 2) :
    ∃ C > 0, ∀ (h : ℂ → ℂ) (x : ℂ), AEStronglyMeasurable h volume →
      Integrable (fun w => ‖h w‖ * ‖w - x‖ ^ (1 - b)) →
      Integrable (fun z => ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖) ∧
      (∫ z, ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖) ≤
        C * ∫ w, ‖h w‖ * ‖w - x‖ ^ (1 - b) := by
  obtain ⟨C, hC, hkernel⟩ := weighted_inverse_kernel hb hb2
  refine ⟨Real.pi⁻¹ * C, by positivity, ?_⟩
  intro h x hh hw
  let G : ℂ × ℂ → ℂ := fun p => ((‖x - p.1‖ ^ (-b) : ℝ) : ℂ) *
    ((p.1 - p.2)⁻¹ * h p.2)
  have hG : AEStronglyMeasurable G (volume.prod volume) := by
    apply AEStronglyMeasurable.mul
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · exact (by fun_prop : Measurable (fun p : ℂ × ℂ => (p.1 - p.2)⁻¹)).aestronglyMeasurable.mul
        hh.comp_snd
  have hnorm (z w : ℂ) : ‖G (z, w)‖ =
      ‖h w‖ * (‖x - z‖ ^ (-b) / ‖z - w‖) := by
    simp only [G, norm_mul, norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (x - z)) (-b)), div_eq_mul_inv]
    ring
  have hne : ∀ᵐ w : ℂ ∂volume, w ≠ x := by
    exact ae_iff.mpr (by simp)
  have hinner : ∀ᵐ w : ℂ ∂volume,
      Integrable (fun z => G (z, w)) ∧
        (∫ z, ‖G (z, w)‖) ≤ C * (‖h w‖ * ‖w - x‖ ^ (1 - b)) := by
    filter_upwards [hne] with w hwx
    obtain ⟨hi, hbnd⟩ := hkernel x w hwx.symm
    constructor
    · apply (hi.const_mul ‖h w‖).mono'
        (by apply Measurable.aestronglyMeasurable; dsimp only [G]; fun_prop)
      filter_upwards [] with z
      exact (hnorm z w).le
    · simp_rw [hnorm, integral_const_mul]
      calc
        _ ≤ ‖h w‖ * (C * ‖w - x‖ ^ (1 - b)) :=
          mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
        _ = _ := by ring
  have hJ : Integrable (fun w => ∫ z, ‖G (z, w)‖) := by
    apply (hw.const_mul C).mono' hG.norm.prod_swap.integral_prod_right'
    filter_upwards [hinner] with w hw'
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hw'.2
  have hiG : Integrable G (volume.prod volume) :=
    (integrable_prod_iff' hG).mpr ⟨hinner.mono (fun _ h' => h'.1), hJ⟩
  have hpoint (z : ℂ) : (Real.pi : ℂ)⁻¹ * (∫ w, G (z, w)) =
      ((‖x - z‖ ^ (-b) : ℝ) : ℂ) * cauchyOperator h z := by
    simp only [G, cauchyOperator, integral_const_mul, smul_eq_mul]
    ring
  have hpointNorm (z : ℂ) : Real.pi⁻¹ * ‖∫ w, G (z, w)‖ =
      ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖ := by
    have hn := congrArg norm (hpoint z)
    simpa only [norm_mul, norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (x - z)) (-b))] using hn
  have hpot : Integrable (fun z => ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖) := by
    apply (hiG.integral_prod_left.norm.const_mul Real.pi⁻¹).congr
    exact ae_of_all _ hpointNorm
  refine ⟨hpot, ?_⟩
  calc
    _ ≤ ∫ z, Real.pi⁻¹ * ∫ w, ‖G (z, w)‖ := by
      apply integral_mono_ae hpot (hiG.integral_norm_prod_left.const_mul Real.pi⁻¹)
      filter_upwards [] with z
      rw [← hpointNorm]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = Real.pi⁻¹ * ∫ w, ∫ z, ‖G (z, w)‖ := by
      rw [integral_const_mul, integral_integral_swap hiG.norm]
    _ ≤ Real.pi⁻¹ * ∫ w, C * (‖h w‖ * ‖w - x‖ ^ (1 - b)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono_ae hJ (hw.const_mul C) (hinner.mono (fun _ h' => h'.2))
    _ = _ := by rw [integral_const_mul, mul_assoc]

end PoincareConjecture.M65Boundary
