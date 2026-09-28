import PoincareConjecture.Proofs.M28.Thm10_2_Counterexamples
import PoincareConjecture.Proofs.M28.Thm10_2_DenseTime

set_option autoImplicit false

universe u

namespace PoincareConjecture.M28

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

end PoincareConjecture.M28
