import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv









set_option autoImplicit false

namespace PoincareConjecture.M60

variable {A v : ℝ → ℝ} {a b c : ℝ}



theorem antitoneOn_exp_mul_of_deriv_le
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivWithinAt A (v t) (Set.Icc a b) t)
    (hbound : ∀ t ∈ Set.Icc a b, v t ≤ c * A t) (anchor : ℝ) :
    AntitoneOn (fun t => Real.exp (-c * (t - anchor)) * A t) (Set.Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt (fun t => Real.exp (-c * (t - anchor)) * A t)
        (Real.exp (-c * (t - anchor)) * (v t - c * A t)) (Set.Icc a b) t := by
    convert! ((((hasDerivAt_id t).sub_const anchor).const_mul (-c)).exp.hasDerivWithinAt.mul
      (hderiv t ht)) using 1
    dsimp only [id, Pi.neg_apply]
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    (sub_nonpos.mpr (hbound t (interior_subset ht)))



theorem monotoneOn_exp_mul_of_le_deriv
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivWithinAt A (v t) (Set.Icc a b) t)
    (hbound : ∀ t ∈ Set.Icc a b, -c * A t ≤ v t) (anchor : ℝ) :
    MonotoneOn (fun t => Real.exp (c * (t - anchor)) * A t) (Set.Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt (fun t => Real.exp (c * (t - anchor)) * A t)
        (Real.exp (c * (t - anchor)) * (v t + c * A t)) (Set.Icc a b) t := by
    convert! ((((hasDerivAt_id t).sub_const anchor).const_mul c).exp.hasDerivWithinAt.mul
      (hderiv t ht)) using 1
    dsimp only [id, Pi.neg_apply]
    ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  apply mul_nonneg (Real.exp_pos _).le
  have h := hbound t (interior_subset ht)
  linarith



theorem le_exp_mul_of_deriv_le
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivWithinAt A (v t) (Set.Icc a b) t)
    (hbound : ∀ t ∈ Set.Icc a b, v t ≤ c * A t)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    A t ≤ Real.exp (c * (t - s)) * A s := by
  have h := antitoneOn_exp_mul_of_deriv_le hderiv hbound s hs ht hst
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at h
  have h' := mul_le_mul_of_nonneg_left h (Real.exp_pos (c * (t - s))).le
  have he : Real.exp (c * (t - s)) * Real.exp (-c * (t - s)) = 1 := by
    rw [← Real.exp_add, show c * (t - s) + -c * (t - s) = 0 by ring, Real.exp_zero]
  rwa [← mul_assoc, he, one_mul] at h'



theorem le_exp_mul_of_le_deriv
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivWithinAt A (v t) (Set.Icc a b) t)
    (hbound : ∀ t ∈ Set.Icc a b, -c * A t ≤ v t)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    A s ≤ Real.exp (c * (t - s)) * A t := by
  simpa only [sub_self, mul_zero, Real.exp_zero, one_mul] using
    monotoneOn_exp_mul_of_le_deriv hderiv hbound s hs ht hst



theorem le_exp_abs_mul_of_abs_deriv_le
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivWithinAt A (v t) (Set.Icc a b) t)
    (hbound : ∀ t ∈ Set.Icc a b, |v t| ≤ c * A t)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    A t ≤ Real.exp (c * |t - s|) * A s := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact le_exp_mul_of_deriv_le hderiv (fun t ht => (abs_le.mp (hbound t ht)).2)
      hs ht hst
  · rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
    exact le_exp_mul_of_le_deriv hderiv (fun t ht => by
      simpa only [neg_mul] using (abs_le.mp (hbound t ht)).1) ht hs hts

end PoincareConjecture.M60
