import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false

namespace PoincareConjecture.M63

theorem exists_uniform_partial_derivative_bounds
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × F → G} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    let f1 := fun p z => (fderiv ℝ f (p, z)).comp (ContinuousLinearMap.inr ℝ E F)
    Continuous (Function.uncurry f1) ∧ ∃ A B : NNReal,
      (∀ p z, HasFDerivAt (fun y => f (p, y)) (f1 p z) z ∧ ‖f1 p z‖ ≤ A) ∧
      ∀ p, LipschitzWith B (f1 p) := by
  let I := ContinuousLinearMap.inr ℝ E F
  have hI : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ E F
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hdf.continuous
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hc.fderiv ℝ) hdf (by norm_num)
  let A : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨hdf.continuous.clm_comp continuous_const, A, B, ?_, ?_⟩
  · intro p z
    refine ⟨?_, ?_⟩
    · have hprod : (0 : F →L[ℝ] E).prod (ContinuousLinearMap.id ℝ F) = I := by
        ext y <;> rfl
      simpa only [Function.comp_def, hprod] using
        (hf.differentiable (by norm_num) (p, z)).hasFDerivAt.comp z
          ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z))
    · calc
        ‖(fderiv ℝ f (p, z)).comp I‖ ≤ ‖fderiv ℝ f (p, z)‖ * ‖I‖ :=
          (fderiv ℝ f (p, z)).opNorm_comp_le I
        _ ≤ ‖fderiv ℝ f (p, z)‖ := by simpa using mul_le_mul_of_nonneg_left hI (norm_nonneg _)
        _ ≤ (A : ℝ) := (hC (p, z)).trans (le_max_left _ _)
  · intro p
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hdist : dist (p, z) (p, w) = dist z w := by
      change max (dist p p) (dist z w) = dist z w
      simp only [dist_self, max_eq_right dist_nonneg]
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
    calc
      _ ≤ ‖fderiv ℝ f (p, z) - fderiv ℝ f (p, w)‖ * ‖I‖ :=
        (fderiv ℝ f (p, z) - fderiv ℝ f (p, w)).opNorm_comp_le I
      _ ≤ ‖fderiv ℝ f (p, z) - fderiv ℝ f (p, w)‖ := by
        simpa using mul_le_mul_of_nonneg_left hI (norm_nonneg _)
      _ ≤ (B : ℝ) * dist z w := by
        simpa only [hdist, dist_eq_norm] using hB.dist_le_mul (p, z) (p, w)

end PoincareConjecture.M63
