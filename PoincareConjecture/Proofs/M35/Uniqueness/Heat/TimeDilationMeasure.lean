import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDilationOperator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

theorem map_timeMeasure_dilation {s : ℝ} (hs : 0 < s) (T : ℝ) :
    Measure.map (fun t : ℝ => s * t) (timeMeasure T) =
      ENNReal.ofReal s⁻¹ • timeMeasure (s * T) := by
  have hpre : (fun t : ℝ => s * t) ⁻¹' Ioc 0 (s * T) = Ioc 0 T := by
    ext t
    simp only [mem_preimage, mem_Ioc, mul_pos_iff_of_pos_left hs, mul_le_mul_iff_right₀ hs]
  change Measure.map (fun t : ℝ => s * t) (volume.restrict (Ioc 0 T)) = _
  rw [← hpre, ← Measure.restrict_map (measurable_const_mul s) measurableSet_Ioc,
    Real.map_volume_mul_left hs.ne', Measure.restrict_smul, abs_of_pos (inv_pos.mpr hs)]

theorem memLp_time_dilation {E : Type*} [NormedAddCommGroup E]
    {s T B : ℝ} (hs : 0 < s) (hsT : s * T ≤ B) {v : ℝ → E}
    (hv : MemLp v 2 (timeMeasure B)) :
    MemLp (fun t => v (s * t)) 2 (timeMeasure T) := by
  have hsmall : MemLp v 2 (timeMeasure (s * T)) :=
    hv.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl hsT))
  have hm : MemLp v 2 (Measure.map (fun t : ℝ => s * t) (timeMeasure T)) := by
    rw [map_timeMeasure_dilation hs T]
    exact hsmall.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (measurable_const_mul s).aemeasurable

theorem ae_time_dilation {s T B : ℝ} (hs : 0 < s) (hsT : s * T ≤ B)
    {P : ℝ → Prop} (hP : ∀ᵐ t ∂timeMeasure B, P t) :
    ∀ᵐ t ∂timeMeasure T, P (s * t) := by
  have hsmall : ∀ᵐ t ∂timeMeasure (s * T), P t :=
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl hsT) hP
  have hm : ∀ᵐ t ∂Measure.map (fun t : ℝ => s * t) (timeMeasure T), P t := by
    rw [map_timeMeasure_dilation hs T]
    exact Measure.ae_smul_measure hsmall _
  exact ae_of_ae_map (measurable_const_mul s).aemeasurable hm

theorem integral_time_dilation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Q : ℝ → E) (s t : ℝ) :
    (∫ r in (0 : ℝ)..t, s • Q (s * r)) = ∫ r in (0 : ℝ)..(s * t), Q r := by
  rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left, mul_zero]

end PoincareConjecture.M35.Uniqueness.Heat
