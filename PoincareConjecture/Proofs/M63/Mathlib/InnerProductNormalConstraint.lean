import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false

open scoped ContDiff RealInnerProductSpace

namespace PoincareConjecture.M63

theorem secondDeriv_normal_constraint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u r : ℝ → E} (hu : ContDiff ℝ 2 u) (hr : ContDiff ℝ ∞ r)
    (hnormal : ∀ x, ⟪u x, deriv r x⟫ = 0) (x : ℝ) :
    ⟪deriv (deriv u) x, deriv r x⟫ =
      -2 * ⟪deriv u x, deriv (deriv r) x⟫ -
        ⟪u x, deriv (deriv (deriv r)) x⟫ := by
  have hr1 : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
  have hr2 : ContDiff ℝ ∞ (deriv (deriv r)) := (contDiff_infty_iff_deriv.mp hr1).2
  have hu0 (y : ℝ) := (hu.differentiable (by norm_num) y).hasDerivAt
  have hu1 (y : ℝ) := (hu.differentiable_deriv_two y).hasDerivAt
  have hdr1 (y : ℝ) := (hr1.differentiable (by simp) y).hasDerivAt
  have hdr2 (y : ℝ) := (hr2.differentiable (by simp) y).hasDerivAt
  have hfirst (y : ℝ) :
      ⟪u y, deriv (deriv r) y⟫ + ⟪deriv u y, deriv r y⟫ = 0 := by
    have hd := (hu0 y).inner ℝ (hdr1 y)
    have heq : (fun z => ⟪u z, deriv r z⟫) = fun _ => (0 : ℝ) := funext hnormal
    rw [heq] at hd
    exact hd.unique (hasDerivAt_const y 0)
  have hd : HasDerivAt
      (fun y => ⟪u y, deriv (deriv r) y⟫ + ⟪deriv u y, deriv r y⟫)
      ((⟪u x, deriv (deriv (deriv r)) x⟫ + ⟪deriv u x, deriv (deriv r) x⟫) +
        (⟪deriv u x, deriv (deriv r) x⟫ + ⟪deriv (deriv u) x, deriv r x⟫)) x :=
    ((hu0 x).inner ℝ (hdr2 x)).fun_add ((hu1 x).inner ℝ (hdr1 x))
  have heq :
      (fun y => ⟪u y, deriv (deriv r) y⟫ + ⟪deriv u y, deriv r y⟫) =
        fun _ => (0 : ℝ) := funext hfirst
  rw [heq] at hd
  have hzero := hd.unique (hasDerivAt_const x 0)
  linarith only [hzero]

end PoincareConjecture.M63
