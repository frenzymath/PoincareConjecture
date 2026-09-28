import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.LowerCurvature
import Mathlib.Tactic.FinCases

noncomputable section
set_option autoImplicit false

namespace Poincare.Alexandrov

theorem comparisonAngle_add_eq_pi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngle a b (a + b) = Real.pi := by
  have hden : Real.sinh a * Real.sinh b ≠ 0 :=
    mul_ne_zero (Real.sinh_pos_iff.mpr ha).ne' (Real.sinh_pos_iff.mpr hb).ne'
  rw [comparisonAngle, Real.cosh_add]
  have hquot :
      (Real.cosh a * Real.cosh b -
        (Real.cosh a * Real.cosh b + Real.sinh a * Real.sinh b)) /
        (Real.sinh a * Real.sinh b) = -1 := by
    apply (div_eq_iff hden).mpr
    ring
  rw [hquot, Real.arccos_neg_one]

theorem comparisonAngle_self_zero {a : ℝ} (ha : 0 < a) :
    comparisonAngle a a 0 = 0 := by
  have hs : Real.sinh a * Real.sinh a ≠ 0 :=
    mul_ne_zero (Real.sinh_pos_iff.mpr ha).ne' (Real.sinh_pos_iff.mpr ha).ne'
  have hnum : Real.cosh a * Real.cosh a - 1 = Real.sinh a * Real.sinh a := by
    nlinarith only [Real.cosh_sq_sub_sinh_sq a]
  rw [comparisonAngle, Real.cosh_zero, hnum, div_self hs, Real.arccos_one]

theorem CurvatureGEnegOne.comparisonAngle_add_le_pi_of_between
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X) {p y z q : X}
    (hpy : p ≠ y) (hyz : 0 < dist y z) (hyq : 0 < dist y q)
    (hbetween : dist z q = dist y z + dist y q) :
    comparisonAngle (dist y p) (dist y z) (dist p z) +
      comparisonAngle (dist y p) (dist y q) (dist p q) ≤ Real.pi := by
  by_cases hpz : p = z
  · subst p
    rw [dist_self, comparisonAngle_self_zero hyz, hbetween,
      comparisonAngle_add_eq_pi hyz hyq, zero_add]
  by_cases hpq : p = q
  · subst p
    rw [dist_self, comparisonAngle_self_zero hyq, add_zero, dist_comm q z, hbetween,
      add_comm (dist y z) (dist y q), comparisonAngle_add_eq_pi hyq hyz]
  have hyz' : y ≠ z := dist_pos.mp hyz
  have hyq' : y ≠ q := dist_pos.mp hyq
  have hzq : z ≠ q := by
    intro heq
    rw [heq, dist_self] at hbetween
    linarith
  let v : Fin 4 → X := ![y, p, z, q]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [v, Ne.symm hpy, Ne.symm hpz, Ne.symm hpq, Ne.symm hyz',
        Ne.symm hyq', Ne.symm hzq]
  have hfour := hX v hv
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hfour
  rw [hbetween, comparisonAngle_add_eq_pi hyz hyq] at hfour
  linarith only [hfour]

theorem CurvatureGEnegOne.comparisonAngle_le_pi_sub_of_between
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X) {p y z q : X}
    (hpy : p ≠ y) (hyz : 0 < dist y z) (hyq : 0 < dist y q)
    (hbetween : dist z q = dist y z + dist y q) :
    comparisonAngle (dist y p) (dist y z) (dist p z) ≤
      Real.pi - comparisonAngle (dist y p) (dist y q) (dist p q) := by
  linarith only [hX.comparisonAngle_add_le_pi_of_between hpy hyz hyq hbetween]

end Poincare.Alexandrov
