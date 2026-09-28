import PoincareConjecture.Proofs.M71.Thm18_1_NegativeTime
import PoincareConjecture.Proofs.M71.WidthInputs

set_option autoImplicit false

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {ancestry : RepairedFiniteAncestryData D.flow W}

theorem m71Profile_neg_at_extinctionTime
    (Q : M71FiniteContinuationService D W ancestry)
    (hM67 : M67SurgeryWidthTheory.{u})
    {hT : m71ExtinctionTime Q ∈ D.flow.time_domain}
    (J : M71ComponentContinuationData D W ancestry Q.basepoint_service
      (m71ExtinctionTime Q) hT) :
    m68Profile (M69FinitePieceInput.profile (m71ClassLedger Q J hM67)
      (m71ComparisonInterval Q J hM67) (m71WidthChoice Q J hM67).2.estimate)
      (m71ExtinctionTime Q) < 0 := by
  change (m71WidthChoice Q J hM67).1.width (m67InitialTime J.P) *
      Real.rpow ((1 + 4 * m71ExtinctionTime Q) / (1 + 4 * (0 : ℝ))) ((3 : ℝ) / 4) +
        2 * Real.pi * Real.rpow (1 + 4 * (0 : ℝ)) ((1 : ℝ) / 4) *
          Real.rpow (1 + 4 * m71ExtinctionTime Q) ((3 : ℝ) / 4) -
        2 * Real.pi * (1 + 4 * m71ExtinctionTime Q) < 0
  rw [m71WidthChoice_initial_width]
  exact (m71ProfileAlgebra_neg (m71InitialWidth Q) (m71InitialWidth_nonneg Q)).2

end PoincareConjecture
