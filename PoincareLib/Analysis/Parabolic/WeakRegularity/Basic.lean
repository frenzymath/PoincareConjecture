/-
Adapted from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source and SHA-256: references/analysis/axel-workspace/weak-parabolic-regularity-sources.json.
Apache-2.0; see the license in that source directory.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Poincare.Analysis.Parabolic.WeakRegularity

abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Spacetime (n : ℕ) := Euclid n × ℝ
abbrev TestFunction (n : ℕ) := Spacetime n → ℝ

end Poincare.Analysis.Parabolic.WeakRegularity
