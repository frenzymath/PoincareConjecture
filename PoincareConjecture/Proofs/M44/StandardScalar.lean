import PoincareConjecture.Definitions.M44CapPersistence

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem RepairedCapPersistenceData.standardScalarRate
    {g₀ : StandardInitialMetric} (P : RepairedCapPersistenceData.{u} g₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 P.standard_cap.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        c / (1 - t) ≤ (P.standard_cap.flow.connection t).scalarCurvature x := by
  obtain ⟨U⟩ := P.standard_cap_uniqueness
  exact U.scalar_lower_bound

end PoincareConjecture
