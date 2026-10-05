import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceData

/-!
# The scalar rate on M44's selected standard flow

Apply its actual M35 output. No uniqueness comparison or new model is needed.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem RepairedCapPersistenceData.standardScalarRate
    {g₀ : StandardInitialMetric} (P : RepairedCapPersistenceData.{u} g₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 P.standard_cap.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        c / (1 - t) ≤ (P.standard_cap.flow.connection t).scalarCurvature x := by
  obtain ⟨U⟩ := P.standard_cap_uniqueness
  exact U.scalar_lower_bound

end PoincareMT
