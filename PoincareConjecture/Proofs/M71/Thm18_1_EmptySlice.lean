import PoincareConjecture.Proofs.M70
import PoincareConjecture.Proofs.M71.WidthInputs

set_option autoImplicit false

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {ancestry : RepairedFiniteAncestryData D.flow W}

theorem m71EmptySlice
    (Q : M71FiniteContinuationService D W ancestry)
    (hM67 : M67SurgeryWidthTheory.{u})
    (hM68 : M68ScalarClockStatement.{u})
    (hM69 : M69FinitePieceStatement.{u})
    (T : ℝ) (hT : T ∈ D.flow.time_domain) (hT_nonneg : 0 ≤ T)
    (hprofile_negative :
      ∀ J : M71ComponentContinuationData D W ancestry Q.basepoint_service T hT,
        m68Profile (M69FinitePieceInput.profile (m71ClassLedger Q J hM67)
          (m71ComparisonInterval Q J hM67) (m71WidthChoice Q J hM67).2.estimate)
          T < 0) :
    IsEmpty (D.flow.slice T).carrier := by
  refine ⟨fun x => ?_⟩
  obtain ⟨n, packages, hcover⟩ := Q.target_cover T hT
  obtain ⟨i, _hi⟩ := hcover x
  let J := packages i
  obtain ⟨C69⟩ := m71FinitePieceApplication Q J hM67 hM68 hM69
  let negative : M70NegativeProfileInput D W J.P (m71ClassLedger Q J hM67)
      (m71ComparisonInterval Q J hM67) (m71WidthChoice Q J hM67).2.estimate C69 :=
    { B := ⟨T, hT_nonneg, le_rfl⟩
      profile_negative := hprofile_negative J
      path_nonempty := ⟨x⟩ }
  exact (Classical.choice (m70FiniteExtinctionContradiction D W J.P
    (m71ClassLedger Q J hM67) (m71ComparisonInterval Q J hM67)
    (m71WidthChoice Q J hM67).2.estimate C69 negative)).contradiction

end PoincareConjecture
