import PoincareLib.Geometry.Alexandrov.Comparison.DistanceChord

/-!
# Comparison angles under radial shortening

Shortening either or both sides of a hinge along metric segments increases
its hyperbolic comparison angle. The proof uses the distance-chord inequality
and the hyperbolic addition formulas. This supports the finite directional
packing argument in Petrunin (2009), Section 3.7, author manuscript p. 7.
-/

set_option autoImplicit false

namespace Poincare.Alexandrov

/-- Shortening one ray of a hinge does not decrease its comparison angle.
The shortened endpoint may equal the original endpoint. -/
theorem CurvatureGEnegOne.comparisonAngle_le_of_radial_shortening
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X)
    {p q r z : X} (hpz : 0 < dist p z) (hpr : 0 < dist p r)
    (hbetween : dist p q = dist p z + dist z q) :
    comparisonAngle (dist p q) (dist p r) (dist q r) ≤
      comparisonAngle (dist p z) (dist p r) (dist z r) := by
  by_cases hzq : z = q
  · subst z
    exact le_rfl
  have htail : 0 < dist z q := dist_pos.mpr hzq
  have hpq : 0 < dist p q := by rw [hbetween]; positivity
  have hchord := hX.cosh_distance_chord_lower_bound (p := r) hpz htail hbetween
  simp only [dist_comm r p, dist_comm r q, dist_comm r z] at hchord
  have hidentity :
      Real.cosh (dist p z) * Real.sinh (dist p q) -
        Real.cosh (dist p q) * Real.sinh (dist p z) = Real.sinh (dist z q) := by
    rw [hbetween, Real.cosh_add, Real.sinh_add]
    linear_combination (Real.sinh (dist z q)) *
      (Real.cosh_sq_sub_sinh_sq (dist p z))
  have hscaled := congrArg (fun a : ℝ => a * Real.cosh (dist p r)) hidentity
  unfold comparisonAngle
  apply Real.arccos_le_arccos
  rw [div_mul_eq_div_div, div_mul_eq_div_div]
  apply (div_le_div_iff_of_pos_right (Real.sinh_pos_iff.mpr hpr)).mpr
  apply (div_le_div_iff₀ (Real.sinh_pos_iff.mpr hpz)
    (Real.sinh_pos_iff.mpr hpq)).mpr
  nlinarith only [hchord, hscaled]

/-- Shortening both rays of a hinge does not decrease its comparison angle. -/
theorem CurvatureGEnegOne.comparisonAngle_le_of_two_radial_shortenings
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X)
    {p q r z w : X} (hpz : 0 < dist p z) (hpw : 0 < dist p w)
    (hz : dist p q = dist p z + dist z q)
    (hw : dist p r = dist p w + dist w r) :
    comparisonAngle (dist p q) (dist p r) (dist q r) ≤
      comparisonAngle (dist p z) (dist p w) (dist z w) := by
  have hpr : 0 < dist p r := by
    rw [hw]
    exact add_pos_of_pos_of_nonneg hpw dist_nonneg
  have hfirst := hX.comparisonAngle_le_of_radial_shortening hpz hpr hz
  have hsecond := hX.comparisonAngle_le_of_radial_shortening hpw hpz hw
  rw [comparisonAngle_comm (dist p r), comparisonAngle_comm (dist p w),
    dist_comm r z, dist_comm w z] at hsecond
  exact hfirst.trans hsecond

end Poincare.Alexandrov
