import PoincareLib.Analysis.ODE.ScalarComparison

/-!
# Differential Harnack path estimates

This module is the real-analysis interface used by the geometric differential
Harnack argument.  The geometric work supplies the scalar curvature along a
path, its time derivative, and the squared path speed.  The two structures
below retain those hypotheses explicitly and expose the finite-start and
ancient endpoint comparisons with the factors appearing in the M06 contract.

The finite estimate is the integrating-factor form of Morgan--Tian,
Theorem 4.37 and Corollary 4.39, p. 81.  The ancient estimate is the
time-origin-free form used in Theorem 4.40, p. 82.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace Poincare.Geometry.RicciFlow.Harnack

/-- Data along a finite time interval satisfying the scalar differential
Harnack inequality.  `f` is scalar curvature and `speedSq` is the squared
spacetime speed of the chosen path. -/
structure FiniteHarnackPath (T a b : ℝ) where
  hTa : T < a
  hab : a ≤ b
  f : ℝ → ℝ
  f' : ℝ → ℝ
  speedSq : ℝ → ℝ
  f_continuous : ContinuousOn f (Icc a b)
  speed_continuous : ContinuousOn speedSq (Ioo a b)
  speed_integrable : IntervalIntegrable speedSq volume a b
  derivative : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t
  differential : ∀ t ∈ Ioo a b,
    0 ≤ f' t + f t / (t - T) + speedSq t / 2 * f t

/-- The integrated finite differential Harnack estimate, including both
elapsed-time factors and allowing `f` to vanish or change sign. -/
theorem FiniteHarnackPath.integrated {T a b : ℝ}
    (H : FiniteHarnackPath T a b) :
    H.f a * (a - T) *
        Real.exp (-(∫ t in a..b, H.speedSq t) / 2) ≤
      H.f b * (b - T) := by
  exact Poincare.ODE.finite_harnack_of_energy_inequality H.hTa H.hab
    H.f_continuous H.speed_continuous H.speed_integrable H.derivative
    H.differential

/-- Data along an ancient time interval satisfying the time-origin-free scalar
differential Harnack inequality. -/
structure AncientHarnackPath (a b : ℝ) where
  hab : a ≤ b
  f : ℝ → ℝ
  f' : ℝ → ℝ
  speedSq : ℝ → ℝ
  f_continuous : ContinuousOn f (Icc a b)
  speed_continuous : ContinuousOn speedSq (Ioo a b)
  speed_integrable : IntervalIntegrable speedSq volume a b
  derivative : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t
  differential : ∀ t ∈ Ioo a b, 0 ≤ f' t + speedSq t / 2 * f t

/-- The integrated ancient differential Harnack estimate. -/
theorem AncientHarnackPath.integrated {a b : ℝ}
    (H : AncientHarnackPath a b) :
    H.f a * Real.exp (-(∫ t in a..b, H.speedSq t) / 2) ≤ H.f b := by
  exact Poincare.ODE.harnack_of_energy_inequality H.hab H.f_continuous
    H.speed_continuous H.speed_integrable H.derivative H.differential

end Poincare.Geometry.RicciFlow.Harnack
