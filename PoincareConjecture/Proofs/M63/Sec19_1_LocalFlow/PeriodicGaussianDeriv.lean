import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianHeat
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv









set_option autoImplicit false

open MeasureTheory Set

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]




theorem hasDerivAt_periodicGaussianHeat (t : ℝ) (f g : C(AddCircle L, E))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (g (x : AddCircle L)) x)
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => periodicGaussianHeat t f (y : AddCircle L))
      (periodicGaussianHeat t g (x : AddCircle L)) x := by
  let Q := fun (y s : ℝ) => gaussianHeatKernel 1 s •
    f ((y : AddCircle L) - ((2 * Real.sqrt t * s : ℝ) : AddCircle L))
  let Q' := fun (y s : ℝ) => gaussianHeatKernel 1 s •
    g ((y : AddCircle L) - ((2 * Real.sqrt t * s : ℝ) : AddCircle L))
  have hi (h : C(AddCircle L, E)) (y : ℝ) :
      Integrable (fun s : ℝ => gaussianHeatKernel 1 s •
        h ((y : AddCircle L) - ((2 * Real.sqrt t * s : ℝ) : AddCircle L))) :=
    (ContinuousMap.evalCLM ℝ (y : AddCircle L)).integrable_comp
      (integrable_periodicGaussian t h)
  have hK : Integrable (gaussianHeatKernel 1) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hder : ∀ s y : ℝ, HasDerivAt (fun z => Q z s) (Q' y s) y := by
    intro s y
    simpa only [Q, Q', Function.comp_def, one_smul, QuotientAddGroup.mk_sub, id_eq] using
      ((hf (y - 2 * Real.sqrt t * s)).scomp y
        ((hasDerivAt_id y).sub_const (2 * Real.sqrt t * s))).fun_const_smul
          (gaussianHeatKernel 1 s)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Q) (F' := Q') (x₀ := x) (s := univ)
    (bound := fun s => gaussianHeatKernel 1 s * ‖g‖) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun y => (hi f y).aestronglyMeasurable))
    (hi f x) (hi g x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s y _ => by
      dsimp only [Q']
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (gaussianHeatKernel_pos (by norm_num) s)]
      exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm g _)
        (gaussianHeatKernel_pos (by norm_num) s).le))
    (hK.mul_const _) (Filter.Eventually.of_forall (fun s y _ => hder s y))
  simpa only [Q, Q', ← periodicGaussianHeat_apply] using h.2

end PoincareConjecture.M63
