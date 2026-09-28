import PoincareConjecture.Proofs.Horizon.Analysis.ODE.ScalarComparison

set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace Poincare.Geometry.RicciFlow.Harnack

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

theorem FiniteHarnackPath.integrated {T a b : ℝ}
    (H : FiniteHarnackPath T a b) :
    H.f a * (a - T) *
        Real.exp (-(∫ t in a..b, H.speedSq t) / 2) ≤
      H.f b * (b - T) := by
  exact Poincare.ODE.finite_harnack_of_energy_inequality H.hTa H.hab
    H.f_continuous H.speed_continuous H.speed_integrable H.derivative
    H.differential

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

theorem AncientHarnackPath.integrated {a b : ℝ}
    (H : AncientHarnackPath a b) :
    H.f a * Real.exp (-(∫ t in a..b, H.speedSq t) / 2) ≤ H.f b := by
  exact Poincare.ODE.harnack_of_energy_inequality H.hab H.f_continuous
    H.speed_continuous H.speed_integrable H.derivative H.differential

end Poincare.Geometry.RicciFlow.Harnack
