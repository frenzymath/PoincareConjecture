import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTraceEstimate







set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]




theorem m64Curve_oscillation_sq_le
    (w d : ℝ → E) (hd : Continuous d) (hw : ∀ t, HasDerivAt w (d t) t)
    {T x y : ℝ} (hx : x ∈ Icc (0 : ℝ) T)
    (hy : y ∈ Icc (0 : ℝ) T) :
    ‖w x - w y‖ ^ 2 ≤ 4 * T * ∫ t in Icc (0 : ℝ) T, ‖d t‖ ^ 2 := by
  let Q := ∫ t in Icc (0 : ℝ) T, ‖d t‖ ^ 2
  have hQ : 0 ≤ Q := integral_nonneg fun t => sq_nonneg ‖d t‖
  have hanchor (z : ℝ) (hz : z ∈ Icc (0 : ℝ) T) : ‖w z - w 0‖ ^ 2 ≤ T * Q := by
    have hFTC : w z - w 0 = ∫ t in (0 : ℝ)..z, d t :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hw t)
        (hd.intervalIntegrable 0 z)).symm
    have hnorm : ‖∫ t in (0 : ℝ)..z, d t‖ ≤ ∫ t in (0 : ℝ)..z, ‖d t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hz.1
    have hnorm0 : 0 ≤ ∫ t in (0 : ℝ)..z, ‖d t‖ :=
      intervalIntegral.integral_nonneg hz.1 fun _ _ => norm_nonneg _
    have hCS := SpectralHeatNative.integral_sq_le_time_mul_integral_sq hz.1
      (hd.norm.intervalIntegrable 0 z) ((hd.norm.pow 2).intervalIntegrable 0 z)
    have hsmall : (∫ t in (0 : ℝ)..z, ‖d t‖ ^ 2) ≤ Q := by
      rw [intervalIntegral.integral_of_le hz.1]
      exact setIntegral_mono_set (hd.norm.pow 2).integrableOn_Icc
        (Eventually.of_forall fun t => sq_nonneg ‖d t‖)
        (Eventually.of_forall fun t ht => ⟨ht.1.le, ht.2.trans hz.2⟩)
    rw [hFTC]
    exact ((sq_le_sq₀ (norm_nonneg _) hnorm0).mpr hnorm).trans
      (hCS.trans ((mul_le_mul_of_nonneg_left hsmall hz.1).trans
        (mul_le_mul_of_nonneg_right hz.2 hQ)))
  have htriangle : ‖w x - w y‖ ≤ ‖w x - w 0‖ + ‖w y - w 0‖ := by
    have hh := norm_sub_le (w x - w 0) (w y - w 0)
    simpa only [sub_sub_sub_cancel_right] using hh
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htriangle
  have hx0 := hanchor x hx
  have hy0 := hanchor y hy
  nlinarith [sq_nonneg (‖w x - w 0‖ - ‖w y - w 0‖)]

end PoincareConjecture
