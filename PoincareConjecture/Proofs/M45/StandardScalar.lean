import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Proofs.M44.StandardScalar








set_option autoImplicit false

universe u

namespace PoincareConjecture

private theorem standardScalarRate_transport
    {g₀ g₁ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {G : MaximalStandardCapFlow g₁}
    (hg : g₀ = g₁) (hF : HEq F G)
    (rate : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 F.base.lifetime,
      ∀ x : StandardCapSpace, c / (1 - t) ≤ (F.connection t).scalarCurvature x) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 G.base.lifetime,
      ∀ x : StandardCapSpace, c / (1 - t) ≤ (G.connection t).scalarCurvature x := by
  cases hg
  cases eq_of_heq hF
  exact rate

theorem RepairedControlledSchedulesData.standardScalarRate
    (S : RepairedControlledSchedulesData.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 S.setup.standard_flow.base.lifetime,
      ∀ x : StandardCapSpace,
        c / (1 - t) ≤ (S.setup.standard_flow.connection t).scalarCurvature x :=
  standardScalarRate_transport S.setup_standard_initial_eq.symm
    S.setup_standard_flow_eq.symm S.cap_persistence.standardScalarRate

end PoincareConjecture
