import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.MorseCoordinates.Factors
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.SquareFactors



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model

private abbrev E2 := EuclideanSpace Real (Fin 2)
open Saddle.Nested

def meridianHeight (a z : Real) (q : E2) : Real :=
  1 + (z + q 0) - (z + q 0)^2 + a * chartRoot z q

def meridianCoefficient (a z : Real) (q : E2) : Real :=
  -1 - a / (meridianRoot (z + q 0) + meridianRoot z) -
    a * z * (2*z + q 0) /
      (meridianRoot z * (meridianRoot (z + q 0) + meridianRoot z)^2)

def transverseCoefficient (a z : Real) (q : E2) : Real :=
  -a / (meridianRoot (z + q 0) + chartRoot z q)

theorem meridianHeight_eq_factors {a z : Real}
    (hz : 0 < 1 - z^2)
    (hcrit : meridianRoot z * (2*z - 1) = -a*z)
    {q : E2} (hq : q ∈ coordinateDomain z) :
    meridianHeight a z q = meridianHeight a z 0 +
      meridianCoefficient a z q * (q 0)^2 + transverseCoefficient a z q * (q 1)^2 := by
  let R := meridianRoot (z + q 0)
  let R₀ := meridianRoot z
  let T := chartRoot z q
  have hR₀ : 0 < R₀ := Real.sqrt_pos.mpr hz
  have hT : 0 < T := Real.sqrt_pos.mpr hq
  have hrad : 0 < 1 - (z + q 0)^2 := by
    change 0 < 1 - (z + q 0)^2 - (q 1)^2 at hq
    nlinarith [sq_nonneg (q 1)]
  have hR : 0 < R := Real.sqrt_pos.mpr hrad
  have hR₂ : R^2 = 1 - (z + q 0)^2 := Real.sq_sqrt hrad.le
  have hR₀₂ : R₀^2 = 1 - z^2 := Real.sq_sqrt hz.le
  have hT₂ : T^2 = 1 - (z + q 0)^2 - (q 1)^2 := Real.sq_sqrt hq.le
  have hsum : R + R₀ ≠ 0 := ne_of_gt (add_pos hR hR₀)
  have hsumT : R + T ≠ 0 := ne_of_gt (add_pos hR hT)
  have hdiff : R₀ - R = (2*z + q 0) * q 0 / (R + R₀) := by
    apply (eq_div_iff hsum).mpr
    nlinarith [hR₂, hR₀₂]
  have hdiffT : R - T = (q 1)^2 / (R + T) := by
    apply (eq_div_iff hsumT).mpr
    nlinarith [hR₂, hT₂]
  have hc : 1 - 2*z = a*z/R₀ := by
    apply (eq_div_iff hR₀.ne').mpr
    dsimp [R₀]
    nlinarith [hcrit]
  have hquot : -a * (2*z + q 0) / (R + R₀) + a*z/R₀ =
      -a * q 0 / (R + R₀) - a*z*(R₀ - R)/(R₀*(R+R₀)) := by
    field_simp
    ring
  have h1 : meridianHeight a z q - meridianHeight a z 0 =
      q 0 * ((1 - 2*z) - q 0 - a*(2*z + q 0)/(R+R₀)) - a*(q 1)^2/(R+T) := by
    have hTform : T = R₀ - (2*z + q 0)*q 0/(R+R₀) - (q 1)^2/(R+T) := by
      linarith [hdiff, hdiffT]
    change (1 + (z + q 0) - (z + q 0)^2 + a*T) -
      (1 + (z + (0 : E2) 0) - (z + (0 : E2) 0)^2 + a*chartRoot z 0) = _
    have hzero : chartRoot z 0 = R₀ := by simp [chartRoot, R₀, meridianRoot]
    rw [hzero]
    conv_lhs => rw [hTform]
    simp only [PiLp.zero_apply, add_zero]
    ring
  have hfactor : meridianHeight a z q - meridianHeight a z 0 =
      meridianCoefficient a z q * (q 0)^2 + transverseCoefficient a z q * (q 1)^2 := by
    rw [h1, hc]
    have hregroup : a*z/R₀-q 0-a*(2*z+q 0)/(R+R₀) =
        -q 0 + (-a*(2*z+q 0)/(R+R₀)+a*z/R₀) := by ring
    rw [hregroup, hquot, hdiff]
    change _ = (-1-a/(R+R₀)-a*z*(2*z+q 0)/(R₀*(R+R₀)^2))*(q 0)^2+
      (-a/(R+T))*(q 1)^2
    field_simp
    ring
  linarith

theorem meridian_coefficients_smooth {a z : Real} (hz : 0 < 1-z^2) :
    ContDiffOn Real ∞ (meridianCoefficient a z) (coordinateDomain z) ∧
      ContDiffOn Real ∞ (transverseCoefficient a z) (coordinateDomain z) := by
  have hR₀ : 0 < meridianRoot z := Real.sqrt_pos.mpr hz
  have hR (q : E2) (hq : q ∈ coordinateDomain z) : 0 < meridianRoot (z+q 0) := by
    apply Real.sqrt_pos.mpr
    change 0 < 1-(z+q 0)^2-(q 1)^2 at hq
    nlinarith [sq_nonneg (q 1)]
  have hT (q : E2) (hq : q ∈ coordinateDomain z) : 0 < chartRoot z q :=
    Real.sqrt_pos.mpr hq
  have hRs : ContDiffOn Real ∞ (fun q : E2 => meridianRoot (z+q 0)) (coordinateDomain z) := by
    apply (show ContDiffOn Real ∞ (fun q : E2 => 1-(z+q 0)^2) _ by fun_prop).sqrt
    exact fun q hq => ne_of_gt (Real.sqrt_pos.mp (hR q hq))
  have hTs : ContDiffOn Real ∞ (chartRoot z) (coordinateDomain z) := by
    apply (show ContDiffOn Real ∞ (fun q : E2 => 1-(z+q 0)^2-(q 1)^2) _ by fun_prop).sqrt
    exact fun q hq => ne_of_gt (Real.sqrt_pos.mp (hT q hq))
  constructor
  · unfold meridianCoefficient
    apply (contDiffOn_const.sub (contDiffOn_const.div (hRs.add contDiffOn_const)
      (fun q hq => ne_of_gt (add_pos (hR q hq) hR₀)))).sub
    apply (show ContDiffOn Real ∞ (fun q : E2 => a*z*(2*z+q 0)) _ by fun_prop).div
      (contDiffOn_const.mul ((hRs.add contDiffOn_const).pow 2))
    exact fun q hq => mul_ne_zero hR₀.ne' (pow_ne_zero _ (ne_of_gt (add_pos (hR q hq) hR₀)))
  · exact contDiffOn_const.div (hRs.add hTs)
      (fun q hq => ne_of_gt (add_pos (hR q hq) (hT q hq)))

theorem meridianCoefficient_zero_ne {a z : Real}
    (ha : a = -(3/10 : Real) ∨ a = 3/10) (hz : 0 < 1-z^2)
    (hcrit : meridianRoot z * (2*z-1) = -a*z) :
    meridianCoefficient a z 0 ≠ 0 := by
  let R := meridianRoot z
  have hR : 0 < R := Real.sqrt_pos.mpr hz
  have hRsq : R^2 = 1-z^2 := Real.sq_sqrt hz.le
  have heq : meridianCoefficient a z 0 = -1-a/(2*R^3) := by
    simp only [meridianCoefficient, PiLp.zero_apply, add_zero]
    change -1-a/(R+R)-a*z*(2*z)/(R*(R+R)^2) = _
    field_simp
    nlinarith [congrArg (fun u : Real => a*u) hRsq]
  rw [heq]
  intro hn
  have haR : a = -2*R^3 := by
    have hden : 2*R^3 ≠ 0 := by positivity
    have he : a/(2*R^3) = -1 := by linarith
    exact (div_eq_iff hden).mp he |>.trans (by ring)
  have hz3 : 2*z^3 = 1 := by
    have hc : R*(2*z-1) = 2*R^3*z := by simpa only [haR, neg_mul, neg_neg] using hcrit
    have hcancel : 2*z-1 = 2*R^2*z := by
      apply (mul_left_cancel₀ hR.ne')
      nlinarith [hc]
    nlinarith [hcancel, congrArg (fun u : Real => u*z) hRsq]
  have hR3 : R^3 = 3/20 := by
    rcases ha with ha | ha
    · linarith
    · have hp : 0 < R^3 := pow_pos hR 3
      linarith
  have hzpos : 0 < z := by nlinarith [sq_nonneg z]
  have hzbound : z < (4/5 : Real) := by
    apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : Real) ≤ 4/5)
    norm_num
    linarith
  have hRbound : R < (11/20 : Real) := by
    apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : Real) ≤ 11/20)
    norm_num
    linarith
  nlinarith [hRsq]

theorem exists_nested_meridian_square_coordinates {a z : Real}
    (ha : a = -(3/10 : Real) ∨ a = 3/10) (hz : 0 < 1-z^2)
    (hcrit : meridianRoot z * (2*z-1) = -a*z) :
    ∃ e : OpenPartialHomeomorph E2 E2, ∃ s t : Real,
      (s = -1 ∨ s = 1) ∧ (t = -1 ∨ t = 1) ∧
      0 ∈ e.source ∧ e 0 = 0 ∧ MapsTo e e.source (coordinateDomain z) ∧
      ContDiffOn Real ∞ e e.source ∧ ContDiffOn Real ∞ e.symm e.target ∧
      ∀ x ∈ e.source, meridianHeight a z (e x) =
        meridianHeight a z 0 + s*(x 0)^2+t*(x 1)^2 := by
  have h0 : (0 : E2) ∈ coordinateDomain z := by simpa [coordinateDomain] using hz
  obtain ⟨hA, hB⟩ := meridian_coefficients_smooth (a := a) hz
  apply exists_signed_square_coordinates_of_factors (isOpen_coordinateDomain z) h0 hA hB
    (meridianCoefficient_zero_ne ha hz hcrit) ?_ (fun q hq => meridianHeight_eq_factors hz hcrit hq)
  unfold transverseCoefficient
  apply div_ne_zero
  · rcases ha with rfl | rfl <;> norm_num
  · exact ne_of_gt (add_pos (Real.sqrt_pos.mpr (by simpa using hz))
      (Real.sqrt_pos.mpr (by simpa [coordinateDomain] using h0)))

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model
