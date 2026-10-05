import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Counterexamples
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTimeTransfer

open scoped PoincareMT.BoundedDistanceSource
/-!
# The conditional same-time assembly

The geometric contradiction must exclude the actual counterexample
sequences, with one accuracy threshold fixed before epsilon, C and A.
This file makes that consumer explicit and derives both frozen estimates
from it. It does not supply the tube/cone contradiction. Reference:
Morgan--Tian Theorem 10.2, pp. 245-265; task derivations 07 and 08.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M28

/-- Excluding the actual divergent counterexample sequences supplies
uniform constants before the flow is selected. This is the final
contradiction step of Theorem 10.2, pp. 246-265; the exclusion is an
explicit hypothesis here. -/
theorem same_time_of_counterexample_exclusion {epsilon₀ : ℝ}
    (hexclude : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
        (∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)) → False) :
    M28SameTimeEstimateStatement.{u} epsilon₀ := by
  by_contra h
  obtain ⟨epsilon, hepsilon, hsmall, C, hC, A, hA, ⟨E⟩⟩ :=
    counterexamples_of_not_same_time h
  exact hexclude epsilon hepsilon hsmall C hC A hA E

/-- One universal accuracy threshold and the geometric sequence
contradiction suffice for the complete frozen M28 theory, using the
checked compact-path dense-time transfer. The geometric exclusion
remains an explicit input (Theorem 10.2; task derivations 07 and 08). -/
theorem theory_of_counterexample_exclusion
    (P : RicciFlowCurvatureTheory.{u}) {epsilon₀ : ℝ}
    (hepsilon₀ : 0 < epsilon₀) (hsmall₀ : epsilon₀ ≤ (1 / 200 : ℝ))
    (hexclude : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
        (∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)) → False) :
    RepairedBoundedDistanceTheory.{u} := by
  have hsame := same_time_of_counterexample_exclusion hexclude
  exact ⟨epsilon₀, hepsilon₀, hsmall₀, hsame, dense_time_of_same_time P hsame⟩

end PoincareMT.M28
