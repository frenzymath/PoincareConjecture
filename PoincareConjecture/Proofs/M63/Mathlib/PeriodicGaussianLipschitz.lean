import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianGradient









set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace PoincareConjecture.M63




theorem periodicGaussianHeat_lipschitz_error_bound
    {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : C(AddCircle L, E)) {k : ℝ≥0}
    (hf : LipschitzWith k (fun x : ℝ => f (x : AddCircle L)))
    {t : ℝ} (_ht : 0 ≤ t) :
    ‖periodicGaussianHeat t f - f‖ ≤
      (k : ℝ) * (∫ z : ℝ, ‖(-2 * z) * gaussianHeatKernel 1 z‖) * Real.sqrt t := by
  have htrans (s : ℝ) : ‖periodicTranslation s f - f‖ ≤ (k : ℝ) * |s| := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change ‖f ((x : AddCircle L) - (s : AddCircle L)) - f (x : AddCircle L)‖ ≤ _
    simpa only [dist_eq_norm, Real.norm_eq_abs, sub_sub_cancel_left, abs_neg,
      QuotientAddGroup.mk_sub] using hf.dist_le_mul (x - s) x
  have hK : Integrable (gaussianHeatKernel 1) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hK1 : Integrable (fun z : ℝ => (-2 * z) * gaussianHeatKernel 1 z) := by
    convert! (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (-2 * (Real.sqrt (Real.pi / 1))⁻¹) using 1
    funext z
    dsimp only [gaussianHeatKernel]
    ring
  have hconstant : (∫ z : ℝ, gaussianHeatKernel 1 z • f) = f := by
    rw [integral_smul_const, integral_gaussianHeatKernel (by norm_num), one_smul]
  have heq : periodicGaussianHeat t f - f =
      ∫ z : ℝ, gaussianHeatKernel 1 z •
        (periodicTranslation (2 * Real.sqrt t * z) f - f) := by
    change (∫ z : ℝ, gaussianHeatKernel 1 z •
      periodicTranslation (2 * Real.sqrt t * z) f) - f = _
    calc
      _ = (∫ z : ℝ, gaussianHeatKernel 1 z •
          periodicTranslation (2 * Real.sqrt t * z) f) -
          ∫ z : ℝ, gaussianHeatKernel 1 z • f := by rw [hconstant]
      _ = _ := by
        rw [← integral_sub (integrable_periodicGaussian t f) (hK.smul_const f)]
        congr 1
        funext z
        exact (smul_sub _ _ _).symm
  rw [heq]
  calc
    _ ≤ ∫ z : ℝ, ((k : ℝ) * Real.sqrt t) *
        ‖(-2 * z) * gaussianHeatKernel 1 z‖ := by
      apply norm_integral_le_of_norm_le (hK1.norm.const_mul _)
      filter_upwards [] with z
      have hpos := gaussianHeatKernel_pos (by norm_num : (0 : ℝ) < 1) z
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      calc
        _ ≤ gaussianHeatKernel 1 z * ((k : ℝ) * |2 * Real.sqrt t * z|) :=
          mul_le_mul_of_nonneg_left (htrans _) hpos.le
        _ = _ := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
          simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t), abs_neg]
          norm_num
          ring
    _ = _ := by rw [integral_const_mul]; ring

end PoincareConjecture.M63
