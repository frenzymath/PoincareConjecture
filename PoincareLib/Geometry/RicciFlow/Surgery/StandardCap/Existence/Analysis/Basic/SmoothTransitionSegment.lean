import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.SmoothTransitionSpeed
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Smooth segments with controlled speed

The standard smooth transition parametrizes the segment from zero to a
vector, remaining constant before and after a prescribed interval.
These elementary estimates supply the connector in Morgan-Tian
Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open scoped ContDiff

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth parametrization of the segment from zero to `z`, used in
the connector of Proposition 12.13, pp. 304-306. -/
noncomputable def smoothSegment (a b : ℝ) (z : E) (s : ℝ) : E :=
  smoothTransition ((s - a) / (b - a)) • z

/-- The entire parametrized segment stays within the endpoint norm
(Proposition 12.13, pp. 304-306). -/
theorem smoothSegment_norm_le (a b : ℝ) (z : E) (s : ℝ) :
    ‖smoothSegment a b z s‖ ≤ ‖z‖ := by
  rw [smoothSegment, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (smoothTransition.nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg z) (smoothTransition.le_one _)

/-- The smooth segment starts at zero (Proposition 12.13, pp. 304-306). -/
theorem smoothSegment_left (a b : ℝ) (z : E) : smoothSegment a b z a = 0 := by
  simp [smoothSegment]

/-- A nondegenerate smooth segment reaches its specified endpoint
(Proposition 12.13, pp. 304-306). -/
theorem smoothSegment_right {a b : ℝ} (hab : a ≠ b) (z : E) :
    smoothSegment a b z b = z := by
  simp [smoothSegment, sub_ne_zero.mpr hab.symm]

/-- The segment is smooth on the whole real line, including its joins
(Proposition 12.13, pp. 304-306). -/
theorem smoothSegment_contDiff (a b : ℝ) (z : E) :
    ContDiff ℝ ∞ (smoothSegment a b z) := by
  exact ((smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
    ((contDiff_id.sub contDiff_const).div_const _)).smul contDiff_const

/-- The actual derivative of the smooth segment
(Proposition 12.13, pp. 304-306). -/
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

/-- A global transition-derivative bound gives the expected inverse-length
speed bound, including both joins (Proposition 12.13, pp. 304-306). -/
theorem smoothSegment_deriv_norm_le {a b C : ℝ} (hab : a < b)
    (hC : ∀ x : ℝ, |deriv smoothTransition x| ≤ C) (z : E) (s : ℝ) :
    ‖deriv (smoothSegment a b z) s‖ ≤ (C / (b - a)) * ‖z‖ := by
  rw [(smoothSegment_hasDerivAt a b z s).deriv, norm_smul, Real.norm_eq_abs,
    abs_div, abs_of_pos (sub_pos.mpr hab)]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (hC _) (sub_pos.mpr hab).le) (norm_nonneg z)

end Real
