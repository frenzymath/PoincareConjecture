import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveOscillation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem m64H1Trace_radius_sq_le
    (u v : ℝ → E) {T : ℝ}
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hFTC : ∀ x ∈ Icc (0 : ℝ) T, u x - u 0 = ∫ t in (0 : ℝ)..x, v t)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) T) :
    ‖u x - u 0‖ ^ 2 ≤ T * ∫ t in Icc (0 : ℝ) T, ‖v t‖ ^ 2 := by
  have hi : IntegrableOn v (Icc (0 : ℝ) T) := hv.integrable (by norm_num)
  have hinorm : IntegrableOn (fun t => ‖v t‖) (Icc (0 : ℝ) T) := hi.norm
  have hsq : IntegrableOn (fun t => ‖v t‖ ^ 2) (Icc (0 : ℝ) T) :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hsub : Icc (0 : ℝ) x ⊆ Icc (0 : ℝ) T := fun _ ht => ⟨ht.1, ht.2.trans hx.2⟩
  have hi' : IntervalIntegrable (fun t => ‖v t‖) volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mpr (hinorm.mono_set hsub)
  have hsq' : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mpr (hsq.mono_set hsub)
  have hnorm : ‖∫ t in (0 : ℝ)..x, v t‖ ≤ ∫ t in (0 : ℝ)..x, ‖v t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hx.1
  have hnorm0 : 0 ≤ ∫ t in (0 : ℝ)..x, ‖v t‖ :=
    intervalIntegral.integral_nonneg hx.1 fun _ _ => norm_nonneg _
  have hCS := SpectralHeatNative.integral_sq_le_time_mul_integral_sq hx.1 hi' hsq'
  have hsmall : (∫ t in (0 : ℝ)..x, ‖v t‖ ^ 2) ≤
      ∫ t in Icc (0 : ℝ) T, ‖v t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hx.1]
    exact setIntegral_mono_set hsq (Eventually.of_forall fun t => sq_nonneg ‖v t‖)
      (Eventually.of_forall fun t ht => ⟨ht.1.le, ht.2.trans hx.2⟩)
  rw [hFTC x hx]
  exact ((sq_le_sq₀ (norm_nonneg _) hnorm0).mpr hnorm).trans
    (hCS.trans ((mul_le_mul_of_nonneg_left hsmall hx.1).trans
      (mul_le_mul_of_nonneg_right hx.2 (integral_nonneg fun t => sq_nonneg ‖v t‖))))

theorem m64H1Trace_oscillation_sq_le
    (u v : ℝ → E) {T : ℝ}
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hFTC : ∀ x ∈ Icc (0 : ℝ) T, u x - u 0 = ∫ t in (0 : ℝ)..x, v t)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) T) (hy : y ∈ Icc (0 : ℝ) T) :
    ‖u x - u y‖ ^ 2 ≤ 4 * T * ∫ t in Icc (0 : ℝ) T, ‖v t‖ ^ 2 := by
  have hx0 := m64H1Trace_radius_sq_le u v hv hFTC hx
  have hy0 := m64H1Trace_radius_sq_le u v hv hFTC hy
  have ht : ‖u x - u y‖ ≤ ‖u x - u 0‖ + ‖u y - u 0‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (u x - u 0) (u y - u 0)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
  nlinarith [sq_nonneg (‖u x - u 0‖ - ‖u y - u 0‖)]

end PoincareConjecture
