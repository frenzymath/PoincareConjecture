import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBudget














set_option autoImplicit false

namespace PoincareConjecture




theorem m64Intrinsic_region_budget_disjunction
    {K mu delta area curvature turning : ℝ}
    (hcurvature : Real.pi / 2 - turning ≤ curvature)
    (hupper : curvature ≤ max K 0 * area)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    mu ≤ area ∨ delta ≤ turning := by
  by_cases harea : mu ≤ area
  · exact Or.inl harea
  · right
    by_contra hturn
    exact m64Intrinsic_region_budget_contradiction
      (lt_of_not_ge harea) hcurvature hupper (lt_of_not_ge hturn) hbudget

end PoincareConjecture
