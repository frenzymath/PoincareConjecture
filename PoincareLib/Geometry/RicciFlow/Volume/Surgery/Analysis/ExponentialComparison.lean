import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/ExponentialComparison.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Exponential comparison from an interior differential inequality

The scalar integrating-factor argument used in Morgan-Tian Lemma 17.12,
p. 410. Only continuity is needed at the interval endpoints. See
`proof-work/tasks/M49/derivations/02-density-evolution.md`.
-/

set_option autoImplicit false

open Set

namespace Real

/-- The differential inequality used in MT Lemma 17.12, p. 410, gives exponential growth. -/
theorem le_exp_mul_of_hasDerivAt_le {f f' : ℝ → ℝ} {a b k : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ k * f t) :
    f b ≤ exp (k * (b - a)) * f a := by
  have hw : AntitoneOn (fun t => exp (-(k * t)) * f t) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      ((continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.mul hc)
      (f' := fun t => exp (-(k * t)) * (f' t - k * f t))
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      have h := (((hasDerivAt_id t).const_mul k).neg.exp).mul (hd t ht')
      exact (h.congr_deriv (by dsimp; ring)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (sub_nonpos.mpr (hbound t ht'))
  have h := mul_le_mul_of_nonneg_left
    (hw ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab) (exp_pos (k * b)).le
  calc
    f b = exp (k * b) * (exp (-(k * b)) * f b) := by
      rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
    _ ≤ exp (k * b) * (exp (-(k * a)) * f a) := h
    _ = exp (k * (b - a)) * f a := by
      rw [← mul_assoc, ← exp_add]
      congr 2
      ring

end Real
