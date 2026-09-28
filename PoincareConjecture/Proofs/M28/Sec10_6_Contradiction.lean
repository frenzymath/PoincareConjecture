import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LimitData
import PoincareConjecture.Proofs.M28.Thm10_2_SameTime










set_option autoImplicit false

universe u

namespace PoincareConjecture.M28




theorem same_time_of_tube_contradiction {epsilon₀ : ℝ}
    (hproduce : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
        (∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)) →
            Nonempty (SingularNeckTubeWitness (2 * epsilon)))
    (hexclude : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      SingularNeckTubeWitness (2 * epsilon) → False) :
    M28SameTimeEstimateStatement.{u} epsilon₀ := by
  apply same_time_of_counterexample_exclusion
  intro epsilon hepsilon hsmall C hC A hA E
  obtain ⟨T⟩ := hproduce epsilon hepsilon hsmall C hC A hA E
  exact hexclude epsilon hepsilon hsmall T

end PoincareConjecture.M28
