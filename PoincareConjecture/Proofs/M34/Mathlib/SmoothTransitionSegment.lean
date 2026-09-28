import PoincareConjecture.Proofs.M34.Mathlib.SmoothTransitionSpeed
import Mathlib.Analysis.Calculus.Deriv.Mul










set_option autoImplicit false

open scoped ContDiff

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def smoothSegment (a b : ℝ) (z : E) (s : ℝ) : E :=
  smoothTransition ((s - a) / (b - a)) • z



theorem smoothSegment_norm_le (a b : ℝ) (z : E) (s : ℝ) :
    ‖smoothSegment a b z s‖ ≤ ‖z‖ := by
  rw [smoothSegment, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (smoothTransition.nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg z) (smoothTransition.le_one _)


theorem smoothSegment_left (a b : ℝ) (z : E) : smoothSegment a b z a = 0 := by
  simp [smoothSegment]



theorem smoothSegment_right {a b : ℝ} (hab : a ≠ b) (z : E) :
    smoothSegment a b z b = z := by
  simp [smoothSegment, sub_ne_zero.mpr hab.symm]



theorem smoothSegment_contDiff (a b : ℝ) (z : E) :
    ContDiff ℝ ∞ (smoothSegment a b z) := by
  exact ((smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
    ((contDiff_id.sub contDiff_const).div_const _)).smul contDiff_const



theorem smoothSegment_hasDerivAt (a b : ℝ) (z : E) (s : ℝ) :
    HasDerivAt (smoothSegment a b z)
      ((deriv smoothTransition ((s - a) / (b - a)) / (b - a)) • z) s := by
  have ht := (smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable
    (by simp)
  have harg := ((hasDerivAt_id s).sub_const a).div_const (b - a)
  change HasDerivAt (fun r => smoothTransition ((r - a) / (b - a)) • z) _ s
  simpa only [Function.comp_apply, id_eq, one_div, div_eq_mul_inv,
    one_mul] using
    ((ht _).hasDerivAt.comp s harg).smul_const z



theorem smoothSegment_deriv_norm_le {a b C : ℝ} (hab : a < b)
    (hC : ∀ x : ℝ, |deriv smoothTransition x| ≤ C) (z : E) (s : ℝ) :
    ‖deriv (smoothSegment a b z) s‖ ≤ (C / (b - a)) * ‖z‖ := by
  rw [(smoothSegment_hasDerivAt a b z s).deriv, norm_smul, Real.norm_eq_abs,
    abs_div, abs_of_pos (sub_pos.mpr hab)]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (hC _) (sub_pos.mpr hab).le) (norm_nonneg z)

end Real
