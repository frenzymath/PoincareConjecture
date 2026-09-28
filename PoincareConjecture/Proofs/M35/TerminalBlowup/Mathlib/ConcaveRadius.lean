import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic













set_option autoImplicit false

open Set Filter

namespace PoincareConjecture.M35

private theorem false_of_nonneg_of_uniform_negative_deriv
    {f f₁ : ℝ → ℝ} {a C : ℝ} (hC : C < 0)
    (hpos : ∀ s, a ≤ s → 0 ≤ f s)
    (hderiv : ∀ s, a ≤ s → HasDerivAt f (f₁ s) s)
    (hbound : ∀ s, a ≤ s → f₁ s ≤ C) : False := by
  let b := a + (f a + 1) / (-C)
  have hab : a ≤ b := le_add_of_nonneg_right
    (div_nonneg (by linarith [hpos a le_rfl]) (neg_pos.mpr hC).le)
  have hgrow := (convex_Ici a).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hderiv s (interior_subset hs)).deriv]
      exact hbound s (interior_subset hs)) a (by simp) b hab hab
  have heq : C * (b - a) = -(f a + 1) := by
    dsimp only [b]
    field_simp [ne_of_lt hC]
    ring
  rw [heq] at hgrow
  linarith [hpos b hab]



theorem radial_derivative_nonneg_of_positive_concave
    {f f₁ f₂ : ℝ → ℝ}
    (hpos : ∀ s, 0 < s → 0 < f s)
    (hderiv : ∀ s, 0 < s → HasDerivAt f (f₁ s) s)
    (hderiv₂ : ∀ s, 0 < s → HasDerivAt f₁ (f₂ s) s)
    (hconcave : ∀ s, 0 < s → f₂ s ≤ 0)
    {s : ℝ} (hs : 0 < s) : 0 ≤ f₁ s := by
  have hanti : AntitoneOn f₁ (Ioi 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (fun r hr => (hderiv₂ r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hderiv₂ r (interior_subset hr)).hasDerivWithinAt)
      (fun r hr => hconcave r (interior_subset hr))
  by_contra hneg
  exact false_of_nonneg_of_uniform_negative_deriv (lt_of_not_ge hneg)
    (fun r hr => (hpos r (hs.trans_le hr)).le)
    (fun r hr => hderiv r (hs.trans_le hr))
    (fun r hr => hanti hs (hs.trans_le hr) hr)




theorem radial_radius_sq_le_of_eventual_scalar_floor
    {f f₁ f₂ : ℝ → ℝ}
    (hpos : ∀ s, 0 < s → 0 < f s)
    (hderiv : ∀ s, 0 < s → HasDerivAt f (f₁ s) s)
    (hderiv₂ : ∀ s, 0 < s → HasDerivAt f₁ (f₂ s) s)
    (hconcave : ∀ s, 0 < s → f₂ s ≤ 0)
    {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ᶠ s in atTop,
      c ≤ 2 * (1 - (f₁ s) ^ 2) / (f s) ^ 2 - 4 * f₂ s / f s)
    {s : ℝ} (hs : 0 < s) : (f s) ^ 2 ≤ 2 / c := by
  have hnonneg (r : ℝ) (hr : 0 < r) : 0 ≤ f₁ r :=
    radial_derivative_nonneg_of_positive_concave hpos hderiv hderiv₂ hconcave hr
  have hmono : MonotoneOn f (Ioi 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (fun r hr => (hderiv r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hderiv r (interior_subset hr)).hasDerivWithinAt)
      (fun r hr => hnonneg r (interior_subset hr))
  by_contra hbad
  have hlarge : 2 < c * (f s) ^ 2 := by
    have h := (div_lt_iff₀ hc).mp (lt_of_not_ge hbad)
    nlinarith
  let C := (2 / f s - c * f s) / 4
  have hC : C < 0 := by
    apply div_neg_of_neg_of_pos _ (by norm_num : (0 : ℝ) < 4)
    apply sub_neg.mpr
    apply (div_lt_iff₀ (hpos s hs)).mpr
    nlinarith
  obtain ⟨a, ha⟩ := eventually_atTop.mp hfloor
  let b := max a s
  have hsb : s ≤ b := le_max_right _ _
  have hab : a ≤ b := le_max_left _ _
  apply false_of_nonneg_of_uniform_negative_deriv (f := f₁) (f₁ := f₂) hC
    (fun r hr => hnonneg r (hs.trans_le (hsb.trans hr)))
    (fun r hr => hderiv₂ r (hs.trans_le (hsb.trans hr)))
  intro r hr
  have hsr : s ≤ r := hsb.trans hr
  have hrpos : 0 < f r := hpos r (hs.trans_le hsr)
  have hfr : f s ≤ f r := hmono hs (hs.trans_le hsr) hsr
  have hscaled := mul_le_mul_of_nonneg_right (ha r (hab.trans hr)) (sq_nonneg (f r))
  have heq :
      (2 * (1 - (f₁ r) ^ 2) / (f r) ^ 2 - 4 * f₂ r / f r) * (f r) ^ 2 =
        2 * (1 - (f₁ r) ^ 2) - 4 * f₂ r * f r := by
    field_simp [hrpos.ne']
  rw [heq] at hscaled
  have hsecond : 4 * f₂ r ≤ 2 / f r - c * f r := by
    apply le_of_mul_le_mul_right (a := f r) _ hrpos
    have hcancel : 2 / f r * f r = 2 := div_mul_cancel₀ _ hrpos.ne'
    nlinarith [sq_nonneg (f₁ r)]
  have hinv : 2 / f r ≤ 2 / f s :=
    div_le_div_of_nonneg_left (by norm_num) (hpos s hs) hfr
  have hmul : c * f s ≤ c * f r := mul_le_mul_of_nonneg_left hfr hc.le
  dsimp only [C]
  linarith

end PoincareConjecture.M35
