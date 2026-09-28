




import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Poincare.Analysis.Parabolic.WeakRegularity

abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Spacetime (n : ℕ) := Euclid n × ℝ
abbrev TestFunction (n : ℕ) := Spacetime n → ℝ

end Poincare.Analysis.Parabolic.WeakRegularity
