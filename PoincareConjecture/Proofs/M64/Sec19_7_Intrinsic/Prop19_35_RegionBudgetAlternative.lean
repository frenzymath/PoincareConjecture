import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBudgetChoice
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBudgetDisjunction














set_option autoImplicit false

namespace PoincareConjecture






theorem m64Intrinsic_exists_region_budget_alternative
    {K delta area curvature turning : ℝ}
    (hdelta : 0 < delta) (hdelta_pi : delta < Real.pi / 2)
    (hcurvature : Real.pi / 2 - turning ≤ curvature)
    (hupper : curvature ≤ max K 0 * area) :
    ∃ mu : ℝ, 0 < mu ∧ (mu ≤ area ∨ delta ≤ turning) := by
  obtain ⟨mu, hmu, hbudget⟩ := m64Intrinsic_exists_region_budget
    hdelta hdelta_pi
  exact ⟨mu, hmu,
    m64Intrinsic_region_budget_disjunction hcurvature hupper hbudget⟩

end PoincareConjecture
