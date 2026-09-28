import PoincareConjecture.Proofs.M35.TerminalBlowup.Mathlib.ConcaveRadius

set_option autoImplicit false

open Set Filter

namespace PoincareConjecture.M35

private theorem false_of_nonneg_of_weighted_negative_deriv
    {f f₁ s v : ℝ → ℝ} {a C : ℝ} (hC : C < 0)
    (hpos : ∀ r, a ≤ r → 0 ≤ f r)
    (hderiv : ∀ r, a ≤ r → HasDerivAt f (v r * f₁ r) r)
    (hs : ∀ r, a ≤ r → HasDerivAt s (v r) r)
    (hv : ∀ r, a ≤ r → 0 ≤ v r)
    (hsinf : Tendsto s atTop atTop)
    (hbound : ∀ r, a ≤ r → f₁ r ≤ C) : False := by
  let F (r : ℝ) := f r - C * s r
  have hd (r : ℝ) (hr : r ∈ Ici a) :
      HasDerivAt F (v r * (f₁ r - C)) r := by
    convert! (hderiv r hr).sub ((hs r hr).const_mul C) using 1
    ring
  have hanti : AntitoneOn F (Ici a) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
      (fun r hr => mul_nonpos_of_nonneg_of_nonpos
        (hv r (interior_subset hr)) (sub_nonpos.mpr (hbound r (interior_subset hr))))
  obtain ⟨b, hb, hslarge⟩ :=
    ((eventually_ge_atTop a).and
      (hsinf.eventually (eventually_gt_atTop (s a + (f a + 1) / (-C))))).exists
  have hdiff : (f a + 1) / (-C) < s b - s a := by linarith
  have hmul := (div_lt_iff₀ (neg_pos.mpr hC)).mp hdiff
  have h := hanti (by simp) hb hb
  dsimp only [F] at h
  nlinarith [hpos b hb]

theorem weighted_radial_derivative_nonneg
    {f f₁ f₂ s v : ℝ → ℝ}
    (hpos : ∀ r, 0 < r → 0 < f r)
    (hderiv : ∀ r, 0 < r → HasDerivAt f (v r * f₁ r) r)
    (hderiv₂ : ∀ r, 0 < r → HasDerivAt f₁ (v r * f₂ r) r)
    (hs : ∀ r, 0 < r → HasDerivAt s (v r) r)
    (hv : ∀ r, 0 < r → 0 < v r)
    (hsinf : Tendsto s atTop atTop)
    (hconcave : ∀ r, 0 < r → f₂ r ≤ 0)
    {r : ℝ} (hr : 0 < r) : 0 ≤ f₁ r := by
  have hanti : AntitoneOn f₁ (Ioi 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (fun u hu => (hderiv₂ u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hderiv₂ u (interior_subset hu)).hasDerivWithinAt)
      (fun u hu => mul_nonpos_of_nonneg_of_nonpos
        (hv u (interior_subset hu)).le (hconcave u (interior_subset hu)))
  by_contra hneg
  exact false_of_nonneg_of_weighted_negative_deriv (lt_of_not_ge hneg)
    (fun u hu => (hpos u (hr.trans_le hu)).le)
    (fun u hu => hderiv u (hr.trans_le hu))
    (fun u hu => hs u (hr.trans_le hu))
    (fun u hu => (hv u (hr.trans_le hu)).le) hsinf
    (fun u hu => hanti hr (hr.trans_le hu) hu)

theorem weighted_radial_radius_sq_le_of_eventual_scalar_floor
    {f f₁ f₂ s v : ℝ → ℝ}
    (hpos : ∀ r, 0 < r → 0 < f r)
    (hderiv : ∀ r, 0 < r → HasDerivAt f (v r * f₁ r) r)
    (hderiv₂ : ∀ r, 0 < r → HasDerivAt f₁ (v r * f₂ r) r)
    (hs : ∀ r, 0 < r → HasDerivAt s (v r) r)
    (hv : ∀ r, 0 < r → 0 < v r)
    (hsinf : Tendsto s atTop atTop)
    (hconcave : ∀ r, 0 < r → f₂ r ≤ 0)
    {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ᶠ r in atTop,
      c ≤ 2 * (1 - (f₁ r) ^ 2) / (f r) ^ 2 - 4 * f₂ r / f r)
    {r : ℝ} (hr : 0 < r) : (f r) ^ 2 ≤ 2 / c := by
  have hnonneg (u : ℝ) (hu : 0 < u) : 0 ≤ f₁ u :=
    weighted_radial_derivative_nonneg hpos hderiv hderiv₂ hs hv hsinf hconcave hu
  have hmono : MonotoneOn f (Ioi 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (fun u hu => (hderiv u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hderiv u (interior_subset hu)).hasDerivWithinAt)
      (fun u hu => mul_nonneg (hv u (interior_subset hu)).le
        (hnonneg u (interior_subset hu)))
  by_contra hbad
  have hlarge : 2 < c * (f r) ^ 2 := by
    have h := (div_lt_iff₀ hc).mp (lt_of_not_ge hbad)
    nlinarith
  let C := (2 / f r - c * f r) / 4
  have hC : C < 0 := by
    apply div_neg_of_neg_of_pos _ (by norm_num : (0 : ℝ) < 4)
    apply sub_neg.mpr
    apply (div_lt_iff₀ (hpos r hr)).mpr
    nlinarith
  obtain ⟨a, ha⟩ := eventually_atTop.mp hfloor
  let b := max a r
  have hrb : r ≤ b := le_max_right _ _
  have hab : a ≤ b := le_max_left _ _
  apply false_of_nonneg_of_weighted_negative_deriv
    (f := f₁) (f₁ := f₂) hC
    (fun u hu => hnonneg u (hr.trans_le (hrb.trans hu)))
    (fun u hu => hderiv₂ u (hr.trans_le (hrb.trans hu)))
    (fun u hu => hs u (hr.trans_le (hrb.trans hu)))
    (fun u hu => (hv u (hr.trans_le (hrb.trans hu))).le) hsinf
  intro u hu
  have hru : r ≤ u := hrb.trans hu
  have hupos : 0 < f u := hpos u (hr.trans_le hru)
  have hfu : f r ≤ f u := hmono hr (hr.trans_le hru) hru
  have hscaled := mul_le_mul_of_nonneg_right (ha u (hab.trans hu)) (sq_nonneg (f u))
  have heq :
      (2 * (1 - (f₁ u) ^ 2) / (f u) ^ 2 - 4 * f₂ u / f u) * (f u) ^ 2 =
        2 * (1 - (f₁ u) ^ 2) - 4 * f₂ u * f u := by
    field_simp [hupos.ne']
  rw [heq] at hscaled
  have hsecond : 4 * f₂ u ≤ 2 / f u - c * f u := by
    apply le_of_mul_le_mul_right (a := f u) _ hupos
    have hcancel : 2 / f u * f u = 2 := div_mul_cancel₀ _ hupos.ne'
    nlinarith [sq_nonneg (f₁ u)]
  have hinv : 2 / f u ≤ 2 / f r :=
    div_le_div_of_nonneg_left (by norm_num) (hpos r hr) hfu
  have hmul : c * f r ≤ c * f u := mul_le_mul_of_nonneg_left hfu hc.le
  dsimp only [C]
  linarith

end PoincareConjecture.M35
