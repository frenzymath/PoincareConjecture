import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper










set_option autoImplicit false

open MeasureTheory

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem integrable_periodicGaussianFirstKernel (t : ℝ) (f : C(AddCircle L, E)) :
    Integrable (fun s : ℝ => ((-2 * s) * gaussianHeatKernel 1 s) •
      periodicTranslation (2 * Real.sqrt t * s) f) := by
  have hK1 : Integrable (fun s : ℝ => (-2 * s) * gaussianHeatKernel 1 s) := by
    convert! (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (-2 * (Real.sqrt (Real.pi / 1))⁻¹) using 1
    funext s
    dsimp only [gaussianHeatKernel]
    ring
  have hKc : Continuous (gaussianHeatKernel 1) :=
    continuous_iff_continuousAt.mpr (fun _ => gaussianHeatKernel_hasDerivAt.continuousAt)
  have hc : Continuous (fun s : ℝ => ((-2 * s) * gaussianHeatKernel 1 s) •
      periodicTranslation (2 * Real.sqrt t * s) f) :=
    ((continuous_const.mul continuous_id).mul hKc).smul
      (continuous_periodicTranslation.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const))
  apply (hK1.norm.mul_const ‖f‖).mono' hc.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [] with s
  rw [norm_smul, (periodicTranslation _).norm_map]

variable [CompleteSpace E]





theorem periodicGaussianHeat_derivative_formula_bound {t : ℝ} (ht : 0 < t)
    (f g : C(AddCircle L, E))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (g (x : AddCircle L)) x) :
    (∀ x : ℝ, periodicGaussianHeat t g (x : AddCircle L) =
      (2 * Real.sqrt t)⁻¹ • ∫ s : ℝ, ((-2 * s) * gaussianHeatKernel 1 s) •
        f ((x : AddCircle L) - ((2 * Real.sqrt t * s : ℝ) : AddCircle L))) ∧
    ‖periodicGaussianHeat t g‖ ≤
      ((∫ s : ℝ, ‖(-2 * s) * gaussianHeatKernel 1 s‖) / (2 * Real.sqrt t)) * ‖f‖ := by
  let A := 2 * Real.sqrt t
  have hA : 0 < A := by dsimp [A]; positivity
  have hK1 : Integrable (fun s : ℝ => (-2 * s) * gaussianHeatKernel 1 s) := by
    convert! (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (-2 * (Real.sqrt (Real.pi / 1))⁻¹) using 1
    funext s
    dsimp only [gaussianHeatKernel]
    ring
  have hi (h : C(AddCircle L, E)) (x : ℝ) :
      Integrable (fun s : ℝ => gaussianHeatKernel 1 s •
        h ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L))) :=
    (ContinuousMap.evalCLM ℝ (x : AddCircle L)).integrable_comp
      (integrable_periodicGaussian t h)
  have hi1 (x : ℝ) : Integrable (fun s : ℝ => ((-2 * s) * gaussianHeatKernel 1 s) •
      f ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L))) :=
    (ContinuousMap.evalCLM ℝ (x : AddCircle L)).integrable_comp
      (integrable_periodicGaussianFirstKernel t f)
  have hformula (x : ℝ) : periodicGaussianHeat t g (x : AddCircle L) =
      A⁻¹ • ∫ s : ℝ, ((-2 * s) * gaussianHeatKernel 1 s) •
        f ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L)) := by
    have hv (s : ℝ) : HasDerivAt
        (fun r : ℝ => f ((x : AddCircle L) - ((A * r : ℝ) : AddCircle L)))
        ((-A) • g ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L))) s := by
      simpa only [Function.comp_def, id_eq, mul_one, QuotientAddGroup.mk_sub] using
        (hf (x - A * s)).scomp s (((hasDerivAt_id s).const_mul A).const_sub x)
    have hiv : Integrable (fun s : ℝ => gaussianHeatKernel 1 s •
        ((-A) • g ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L)))) := by
      convert! (hi g x).smul (-A) using 1
      funext s
      exact smul_comm _ _ _
    have h := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (u := gaussianHeatKernel 1) (u' := fun s => (-2 * s) * gaussianHeatKernel 1 s)
      (v := fun s : ℝ => f ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L)))
      (v' := fun s : ℝ => (-A) • g ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L)))
      (fun s _ => by simpa only [mul_one] using
        (gaussianHeatKernel_hasDerivAt (b := 1) (x := s)))
      (fun s _ => hv s) hiv (hi1 x) (hi f x)
    simp only [ContinuousLinearMap.lsmul_apply] at h
    simp_rw [smul_comm (gaussianHeatKernel 1 _) (-A)] at h
    rw [integral_smul] at h
    have heq : A • periodicGaussianHeat t g (x : AddCircle L) =
        ∫ s : ℝ, ((-2 * s) * gaussianHeatKernel 1 s) •
          f ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L)) := by
      rw [periodicGaussianHeat_apply]
      simpa only [A, neg_smul, neg_inj] using h
    calc
      _ = A⁻¹ • (A • periodicGaussianHeat t g (x : AddCircle L)) := by
        rw [smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
      _ = _ := congrArg (fun z => A⁻¹ • z) heq
  refine ⟨hformula, (ContinuousMap.norm_le _ (by positivity)).mpr ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [hformula, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA)]
  have hnorm : ‖∫ s : ℝ, ((-2 * s) * gaussianHeatKernel 1 s) •
      f ((x : AddCircle L) - ((A * s : ℝ) : AddCircle L))‖ ≤
      (∫ s : ℝ, ‖(-2 * s) * gaussianHeatKernel 1 s‖) * ‖f‖ := by
    calc
      _ ≤ ∫ s : ℝ, ‖(-2 * s) * gaussianHeatKernel 1 s‖ * ‖f‖ := by
        apply norm_integral_le_of_norm_le (hK1.norm.mul_const ‖f‖)
        filter_upwards [] with s
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  calc
    _ ≤ A⁻¹ * ((∫ s : ℝ, ‖(-2 * s) * gaussianHeatKernel 1 s‖) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hA.le)
    _ = _ := by dsimp only [A]; ring

end PoincareConjecture.M63
