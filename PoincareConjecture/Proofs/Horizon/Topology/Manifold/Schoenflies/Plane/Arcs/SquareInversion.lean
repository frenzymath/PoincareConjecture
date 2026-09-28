import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Basic

noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.PlaneArcs

private abbrev E2 := EuclideanSpace Real (Fin 2)

def squareGauge (x : E2) : Real := max |x 0| |x 1|

def squareInversion (r : Real) (x : E2) : E2 := (r / squareGauge x) ^ 2 • x

theorem squareGauge_nonneg (x : E2) : 0 ≤ squareGauge x :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem continuous_squareGauge : Continuous squareGauge :=
  (EuclideanSpace.proj 0).continuous.abs.max (EuclideanSpace.proj 1).continuous.abs

theorem squareGauge_smul (a : Real) (x : E2) :
    squareGauge (a • x) = |a| * squareGauge x := by
  simp only [squareGauge, PiLp.smul_apply, smul_eq_mul, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg a)).symm

theorem squareGauge_inversion {r : Real} (hr : 0 < r) {x : E2}
    (hx : 0 < squareGauge x) : squareGauge (squareInversion r x) = r ^ 2 / squareGauge x := by
  rw [squareInversion, squareGauge_smul, abs_of_nonneg (sq_nonneg _)]
  field_simp

theorem squareInversion_involutive_at {r : Real} (hr : 0 < r) {x : E2}
    (hx : 0 < squareGauge x) : squareInversion r (squareInversion r x) = x := by
  have hg := squareGauge_inversion hr hx
  change (r / squareGauge (squareInversion r x)) ^ 2 •
    ((r / squareGauge x) ^ 2 • x) = x
  rw [hg, smul_smul]
  have hscale : (r / (r ^ 2 / squareGauge x)) ^ 2 * (r / squareGauge x) ^ 2 = 1 := by
    field_simp
  rw [hscale, one_smul]

theorem squareInversion_injOn {r : Real} (hr : 0 < r) :
    InjOn (squareInversion r) {x | 0 < squareGauge x} := by
  intro x hx y hy hxy
  have hh := congrArg (squareInversion r) hxy
  simpa only [squareInversion_involutive_at hr hx, squareInversion_involutive_at hr hy] using hh

theorem continuousOn_squareInversion {r : Real} (hr : 0 < r) :
    ContinuousOn (squareInversion r) {x | r ≤ squareGauge x} := by
  apply (((continuousOn_const.div continuous_squareGauge.continuousOn
    (fun x hx => ne_of_gt (hr.trans_le hx))).pow 2).smul continuousOn_id)

theorem squareInversion_fixed {r : Real} (hr : 0 < r) {x : E2}
    (hx : squareGauge x = r) : squareInversion r x = x := by
  simp [squareInversion, hx, ne_of_gt hr]

theorem squareInversion_mem_square {r : Real} (hr : 0 < r) {x : E2}
    (hx : r ≤ squareGauge x) :
    |squareInversion r x 0| ≤ r ∧ |squareInversion r x 1| ≤ r := by
  have hm : 0 < squareGauge x := hr.trans_le hx
  have hbound : squareGauge (squareInversion r x) ≤ r := by
    rw [squareGauge_inversion hr hm, div_le_iff₀ hm]
    nlinarith
  exact ⟨(le_max_left _ _).trans hbound, (le_max_right _ _).trans hbound⟩

end Poincare.Manifold.Schoenflies.PlaneArcs
