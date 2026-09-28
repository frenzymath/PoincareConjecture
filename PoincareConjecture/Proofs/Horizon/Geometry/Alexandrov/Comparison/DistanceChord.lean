import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.Collinear


set_option autoImplicit false

namespace Poincare.Alexandrov




theorem CurvatureGEnegOne.cosh_distance_chord_lower_bound
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X) {p y z q : X}
    (ht : 0 < dist y z) (hs : 0 < dist z q)
    (hbetween : dist y q = dist y z + dist z q) :
    Real.cosh (dist p y) * Real.sinh (dist z q) +
      Real.cosh (dist p q) * Real.sinh (dist y z) ≤
        Real.cosh (dist p z) * Real.sinh (dist y q) := by
  by_cases hpz : p = z
  · subst p
    rw [dist_self, Real.cosh_zero, one_mul, hbetween, Real.sinh_add, dist_comm z y]
    ring_nf
    exact le_rfl
  have ha : 0 < dist z p := dist_pos.mpr (Ne.symm hpz)
  have htz : 0 < dist z y := by simpa only [dist_comm z y] using ht
  have hbetween' : dist y q = dist z y + dist z q := by
    simpa only [dist_comm z y] using hbetween
  have hangle := hX.comparisonAngle_le_pi_sub_of_between hpz htz hs hbetween'
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngle_nonneg (dist z p) (dist z y) (dist p y))
    (show Real.pi - comparisonAngle (dist z p) (dist z q) (dist p q) ≤ Real.pi by
      linarith only [comparisonAngle_nonneg (dist z p) (dist z q) (dist p q)]) hangle
  rw [Real.cos_pi_sub,
    cos_comparisonAngle ha htz dist_nonneg
      (by simpa only [dist_comm p z, dist_comm y z] using abs_dist_sub_le p y z)
      (by simpa only [dist_comm p z] using dist_triangle p z y),
    cos_comparisonAngle ha hs dist_nonneg
      (by simpa only [dist_comm p z, dist_comm q z] using abs_dist_sub_le p q z)
      (by simpa only [dist_comm p z] using dist_triangle p z q)] at hcos
  have hden : 0 < Real.sinh (dist z p) * Real.sinh (dist z y) * Real.sinh (dist z q) :=
    mul_pos (mul_pos (Real.sinh_pos_iff.mpr ha) (Real.sinh_pos_iff.mpr htz))
      (Real.sinh_pos_iff.mpr hs)
  have hmul := mul_le_mul_of_nonneg_right hcos hden.le
  have hap : Real.sinh (dist z p) ≠ 0 := (Real.sinh_pos_iff.mpr ha).ne'
  have hty : Real.sinh (dist z y) ≠ 0 := (Real.sinh_pos_iff.mpr htz).ne'
  have hsq : Real.sinh (dist z q) ≠ 0 := (Real.sinh_pos_iff.mpr hs).ne'
  field_simp [hap, hty, hsq] at hmul
  rw [hbetween', Real.sinh_add, dist_comm p z]
  rw [dist_comm y z]
  nlinarith only [hmul]

end Poincare.Alexandrov
