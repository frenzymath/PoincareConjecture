import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalPoint
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SquareCompletion

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

def meridianRoot (z : Real) : Real := Real.sqrt (1 - z^2)

def chartRoot (z : Real) (q : E2) : Real :=
  Real.sqrt (1 - (z + q 0)^2 - (q 1)^2)

def chartHeight (z : Real) (q : E2) : Real :=
  1 + (z + q 0) - (z + q 0)^2 - (3 / 10) * chartRoot z q

def negativeCoefficient (z : Real) (q : E2) : Real :=
  1 - (3 / 10) / (meridianRoot (z + q 0) + meridianRoot z) -
    (3 / 10) * z * (2*z + q 0) /
      (meridianRoot z * (meridianRoot (z + q 0) + meridianRoot z)^2)

def positiveCoefficient (z : Real) (q : E2) : Real :=
  (3 / 10) / (meridianRoot (z + q 0) + chartRoot z q)

def coordinateDomain (z : Real) : Set E2 :=
  {q | 0 < 1 - (z + q 0)^2 - (q 1)^2}

theorem isOpen_coordinateDomain (z : Real) : IsOpen (coordinateDomain z) := by
  apply isOpen_lt continuous_const
  fun_prop

theorem chartHeight_eq_signed_factors {z : Real}
    (hz : 0 < 1 - z^2)
    (hcrit : meridianRoot z * (2*z - 1) = (3 / 10) * z)
    {q : E2} (hq : q ∈ coordinateDomain z) :
    chartHeight z q = chartHeight z 0 - negativeCoefficient z q * (q 0)^2 +
      positiveCoefficient z q * (q 1)^2 := by
  let R := meridianRoot (z + q 0)
  let R₀ := meridianRoot z
  let T := chartRoot z q
  have hR₀ : 0 < R₀ := Real.sqrt_pos.mpr hz
  have hT : 0 < T := Real.sqrt_pos.mpr hq
  have hrad : 0 < 1 - (z + q 0)^2 := by
    have h := hq
    change 0 < 1 - (z + q 0)^2 - (q 1)^2 at h
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
  have hc : 1 - 2*z = -(3 / 10) * z / R₀ := by
    apply (eq_div_iff hR₀.ne').mpr
    change meridianRoot z * (2*z - 1) = (3 / 10) * z at hcrit
    dsimp [R₀]
    nlinarith [hcrit]
  have hquot : (3 / 10 : Real) * (2*z + q 0) / (R + R₀) - (3 / 10) * z / R₀ =
      (3 / 10) * q 0 / (R + R₀) + (3 / 10) * z * (R₀ - R) / (R₀ * (R + R₀)) := by
    field_simp
    ring
  have h1 : chartHeight z q - chartHeight z 0 =
      q 0 * ((1 - 2*z) - q 0 + (3 / 10) * (2*z + q 0) / (R + R₀)) +
        (3 / 10) * (q 1)^2 / (R + T) := by
    have hTform : T = R₀ - (2*z + q 0)*q 0/(R + R₀) - (q 1)^2/(R + T) := by
      linarith [hdiff, hdiffT]
    change (1 + (z + q 0) - (z + q 0)^2 - (3 / 10)*T) -
      (1 + (z + (0 : E2) 0) - (z + (0 : E2) 0)^2 -
        (3 / 10)*chartRoot z 0) = _
    have hzero : chartRoot z 0 = R₀ := by simp [chartRoot, R₀, meridianRoot]
    rw [hzero]
    conv_lhs => rw [hTform]
    simp only [PiLp.zero_apply, add_zero]
    ring
  have hfactor : chartHeight z q - chartHeight z 0 =
      -negativeCoefficient z q * (q 0)^2 + positiveCoefficient z q * (q 1)^2 := by
    rw [h1, hc]
    have hregroup : -(3 / 10 : Real)*z/R₀ - q 0 + (3 / 10)*(2*z+q 0)/(R+R₀) =
        -q 0 + ((3 / 10)*(2*z+q 0)/(R+R₀) - (3 / 10)*z/R₀) := by ring
    rw [hregroup, hquot, hdiff]
    change _ = -(1 - (3 / 10)/(R+R₀) - (3 / 10)*z*(2*z+q 0)/(R₀*(R+R₀)^2))*
      (q 0)^2 + ((3 / 10)/(R+T))*(q 1)^2
    field_simp
    ring
  linarith

theorem coefficients_smooth {z : Real} (hz : 0 < 1 - z^2) :
    ContDiffOn Real ∞ (negativeCoefficient z) (coordinateDomain z) ∧
      ContDiffOn Real ∞ (positiveCoefficient z) (coordinateDomain z) := by
  have hR₀ : 0 < meridianRoot z := Real.sqrt_pos.mpr hz
  have hR (q : E2) (hq : q ∈ coordinateDomain z) : 0 < meridianRoot (z + q 0) := by
    apply Real.sqrt_pos.mpr
    change 0 < 1 - (z + q 0)^2 - (q 1)^2 at hq
    nlinarith [sq_nonneg (q 1)]
  have hT (q : E2) (hq : q ∈ coordinateDomain z) : 0 < chartRoot z q :=
    Real.sqrt_pos.mpr hq
  have hRs : ContDiffOn Real ∞ (fun q : E2 => meridianRoot (z + q 0)) (coordinateDomain z) := by
    apply (show ContDiffOn Real ∞ (fun q : E2 => 1 - (z + q 0)^2) _ by fun_prop).sqrt
    exact fun q hq => ne_of_gt (Real.sqrt_pos.mp (hR q hq))
  have hTs : ContDiffOn Real ∞ (chartRoot z) (coordinateDomain z) := by
    apply (show ContDiffOn Real ∞ (fun q : E2 => 1 - (z + q 0)^2 - (q 1)^2) _ by fun_prop).sqrt
    exact fun q hq => ne_of_gt (Real.sqrt_pos.mp (hT q hq))
  constructor
  · unfold negativeCoefficient
    apply (contDiffOn_const.sub (contDiffOn_const.div
      (hRs.add contDiffOn_const) (fun q hq => ne_of_gt (add_pos (hR q hq) hR₀)))).sub
    apply (show ContDiffOn Real ∞ (fun q : E2 => (3 / 10)*z*(2*z+q 0)) _ by fun_prop).div
      (contDiffOn_const.mul ((hRs.add contDiffOn_const).pow 2))
    intro q hq
    exact mul_ne_zero hR₀.ne' (pow_ne_zero _ (ne_of_gt (add_pos (hR q hq) hR₀)))
  · exact contDiffOn_const.div (hRs.add hTs) (fun q hq => ne_of_gt (add_pos (hR q hq) (hT q hq)))

theorem negativeCoefficient_zero_pos {z : Real} (hl : (3 / 5 : Real) < z) (hu : z < 5 / 8) :
    0 < negativeCoefficient z 0 := by
  have hz : 0 < 1 - z^2 := by nlinarith
  have hR : 0 < meridianRoot z := Real.sqrt_pos.mpr hz
  have hRsq : (meridianRoot z)^2 = 1-z^2 := Real.sq_sqrt hz.le
  have hRbound : (3 / 4 : Real) < meridianRoot z := by nlinarith
  have hcube : (3 / 10 : Real) < 2 * (meridianRoot z)^3 := by
    have hs : (3 / 4 : Real)^2 < (meridianRoot z)^2 := by nlinarith
    have hm := mul_lt_mul_of_pos_left hs hR
    nlinarith
  have heq : negativeCoefficient z 0 = 1 - (3 / 10)/(2*(meridianRoot z)^3) := by
    simp only [negativeCoefficient, PiLp.zero_apply, add_zero]
    field_simp
    nlinarith [hRsq]
  rw [heq]
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hcube)

theorem positiveCoefficient_pos {z : Real} {q : E2} (hq : q ∈ coordinateDomain z) :
    0 < positiveCoefficient z q :=
  div_pos (by norm_num) (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hq))

end Poincare.Manifold.Schoenflies.Saddle.Nested
