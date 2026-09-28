import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv










namespace Poincare

open Set



theorem abs_log_sub_le_of_abs_deriv_le_mul
    {f f' : ℝ → ℝ} {s : Set ℝ} {C x y : ℝ}
    (hs : Convex ℝ s) (hpos : ∀ t ∈ s, 0 < f t)
    (hderiv : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t)
    (hbound : ∀ t ∈ s, |f' t| ≤ C * f t)
    (hx : x ∈ s) (hy : y ∈ s) :
    |Real.log (f y) - Real.log (f x)| ≤ C * |y - x| := by
  have hlog : ∀ t ∈ s,
      HasDerivWithinAt (fun u ↦ Real.log (f u)) (f' t / f t) s t := by
    intro t ht
    exact (hderiv t ht).log (ne_of_gt (hpos t ht))
  have hquot : ∀ t ∈ s, ‖f' t / f t‖ ≤ C := by
    intro t ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos t ht)]
    exact (div_le_iff₀ (hpos t ht)).2 (hbound t ht)
  simpa only [Real.norm_eq_abs] using
    hs.norm_image_sub_le_of_norm_hasDerivWithin_le hlog hquot hx hy



theorem exp_bounds_of_abs_deriv_le_mul
    {f f' : ℝ → ℝ} {s : Set ℝ} {C x y : ℝ}
    (hs : Convex ℝ s) (hpos : ∀ t ∈ s, 0 < f t)
    (hderiv : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t)
    (hbound : ∀ t ∈ s, |f' t| ≤ C * f t)
    (hx : x ∈ s) (hy : y ∈ s) :
    Real.exp (-C * |y - x|) * f x ≤ f y ∧
      f y ≤ Real.exp (C * |y - x|) * f x := by
  have hlog := abs_le.mp
    (abs_log_sub_le_of_abs_deriv_le_mul hs hpos hderiv hbound hx hy)
  constructor
  · have h : -C * |y - x| + Real.log (f x) ≤ Real.log (f y) := by
      linarith [hlog.1]
    simpa only [Real.exp_add, Real.exp_log (hpos x hx), Real.exp_log (hpos y hy)]
      using Real.exp_le_exp.mpr h
  · have h : Real.log (f y) ≤ C * |y - x| + Real.log (f x) := by
      linarith [hlog.2]
    simpa only [Real.exp_add, Real.exp_log (hpos x hx), Real.exp_log (hpos y hy)]
      using Real.exp_le_exp.mpr h

end Poincare
