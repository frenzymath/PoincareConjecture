import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTranslation
import PoincareConjecture.Proofs.M03.Existence.HeatKernelNative
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap










set_option autoImplicit false

open MeasureTheory

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in



theorem integrable_periodicGaussian (t : ℝ) (f : C(AddCircle L, E)) :
    Integrable (fun s : ℝ => gaussianHeatKernel 1 s •
      periodicTranslation (2 * Real.sqrt t * s) f) := by
  have hK : Integrable (gaussianHeatKernel 1) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hc : Continuous (fun s : ℝ => gaussianHeatKernel 1 s •
      periodicTranslation (2 * Real.sqrt t * s) f) := by
    have hKc : Continuous (gaussianHeatKernel 1) :=
      continuous_iff_continuousAt.mpr (fun _ => gaussianHeatKernel_hasDerivAt.continuousAt)
    have htrans : Continuous (fun s : ℝ => periodicTranslation (2 * Real.sqrt t * s) f) :=
      continuous_periodicTranslation.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const)
    exact hKc.smul htrans
  apply (hK.mul_const ‖f‖).mono' hc.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [] with s
  rw [norm_smul, (periodicTranslation _).norm_map, Real.norm_eq_abs,
    abs_of_pos (gaussianHeatKernel_pos (by norm_num) s)]

omit [CompleteSpace E] in


theorem norm_integral_periodicGaussian_le (t : ℝ) (f : C(AddCircle L, E)) :
    ‖∫ s : ℝ, gaussianHeatKernel 1 s •
      periodicTranslation (2 * Real.sqrt t * s) f‖ ≤ ‖f‖ := by
  have hK : Integrable (gaussianHeatKernel 1) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _
  calc
    _ ≤ ∫ s : ℝ, gaussianHeatKernel 1 s * ‖f‖ := by
      apply norm_integral_le_of_norm_le (hK.mul_const _)
      filter_upwards [] with s
      rw [norm_smul, (periodicTranslation _).norm_map, Real.norm_eq_abs,
        abs_of_pos (gaussianHeatKernel_pos (by norm_num) s)]
    _ = ‖f‖ := by
      rw [integral_mul_const, integral_gaussianHeatKernel (by norm_num), one_mul]




noncomputable def periodicGaussianHeat (t : ℝ) :
    C(AddCircle L, E) →L[ℝ] C(AddCircle L, E) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ s : ℝ, gaussianHeatKernel 1 s •
        periodicTranslation (2 * Real.sqrt t * s) f
      map_add' := by
        intro f g
        simp only [map_add, smul_add]
        exact integral_add (integrable_periodicGaussian t f) (integrable_periodicGaussian t g)
      map_smul' := by
        intro c f
        simp only [map_smul, RingHom.id_apply, smul_comm (gaussianHeatKernel 1 _) c]
        exact integral_smul c _ }
    1 (fun f => by simpa using norm_integral_periodicGaussian_le t f)



theorem periodicGaussianHeat_apply (t : ℝ) (f : C(AddCircle L, E)) (x : AddCircle L) :
    periodicGaussianHeat t f x = ∫ s : ℝ, gaussianHeatKernel 1 s •
      f (x - ((2 * Real.sqrt t * s : ℝ) : AddCircle L)) := by
  exact ((ContinuousMap.evalCLM ℝ x).integral_comp_comm
    (integrable_periodicGaussian t f)).symm




theorem periodicGaussianHeat_properties (f : C(AddCircle L, E)) :
    (∀ t : ℝ, ‖periodicGaussianHeat t f‖ ≤ ‖f‖) ∧
      periodicGaussianHeat 0 f = f ∧ Continuous (fun t : ℝ => periodicGaussianHeat t f) := by
  refine ⟨fun t => norm_integral_periodicGaussian_le t f, ?_, ?_⟩
  · ext x
    rw [periodicGaussianHeat_apply]
    simp only [Real.sqrt_zero, mul_zero, zero_mul, AddCircle.coe_zero, sub_zero]
    rw [integral_smul_const, integral_gaussianHeatKernel (by norm_num), one_smul]
  · have hK : Integrable (gaussianHeatKernel 1) :=
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _
    apply continuous_of_dominated (fun t => (integrable_periodicGaussian t f).aestronglyMeasurable)
      (bound := fun s => gaussianHeatKernel 1 s * ‖f‖)
    · intro t
      filter_upwards [] with s
      rw [norm_smul, (periodicTranslation _).norm_map, Real.norm_eq_abs,
        abs_of_pos (gaussianHeatKernel_pos (by norm_num) s)]
    · exact hK.mul_const _
    · filter_upwards [] with s
      have htrans : Continuous (fun t : ℝ => periodicTranslation (2 * Real.sqrt t * s) f) :=
        continuous_periodicTranslation.comp
          (((continuous_const.mul Real.continuous_sqrt).mul continuous_const).prodMk
            continuous_const)
      exact (continuous_const : Continuous (fun _ : ℝ => gaussianHeatKernel 1 s)).smul htrans

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]




theorem periodicGaussianHeat_comp (A : E →L[ℝ] F) (t : ℝ) (f : C(AddCircle L, E)) :
    periodicGaussianHeat t (A.compLeftContinuous ℝ (AddCircle L) f) =
      A.compLeftContinuous ℝ (AddCircle L) (periodicGaussianHeat t f) := by
  change (∫ s : ℝ, gaussianHeatKernel 1 s • periodicTranslation (2 * Real.sqrt t * s)
    (A.compLeftContinuous ℝ (AddCircle L) f)) =
      A.compLeftContinuous ℝ (AddCircle L)
        (∫ s : ℝ, gaussianHeatKernel 1 s • periodicTranslation (2 * Real.sqrt t * s) f)
  rw [← (A.compLeftContinuous ℝ (AddCircle L)).integral_comp_comm
    (integrable_periodicGaussian t f)]
  congr 1
  funext s
  ext x
  exact (A.map_smul (gaussianHeatKernel 1 s) _).symm

end PoincareConjecture.M63
