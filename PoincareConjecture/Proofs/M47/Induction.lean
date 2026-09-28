import PoincareConjecture.Statements.M47CanonicalInduction
import PoincareConjecture.Proofs.M47.ScalarPersistenceProof
import PoincareConjecture.Proofs.M47.PositiveGradientTerminal
import PoincareConjecture.Proofs.M47.ComponentEstimateProof











set_option autoImplicit false

universe u

namespace PoincareConjecture.Proofs.M47



theorem canonicalOn_of_firstFailure
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) (T0 r : ℝ)
    (first_failure :
      ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r →
        ∃ t ∈ Set.Ico T0 O.H,
          SurgeryCanonicalOn F (Set.Ico 0 t) r ∧
          ∃ x : (F.slice t).carrier,
            r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
            ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (canonical_at_first_failure :
      ∀ t ∈ Set.Ico T0 O.H, SurgeryCanonicalOn F (Set.Ico 0 t) r →
        ∀ x : (F.slice t).carrier,
          r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
          SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C) :
    SurgeryCanonicalOn F (surgeryObservationInterval O) r := by
  by_contra hfail
  obtain ⟨t, ht, hearlier, x, hscalar, hbad⟩ := first_failure hfail
  exact hbad (canonical_at_first_failure t ht hearlier x hscalar)




theorem canonicalInduction_of_uniform_extension
    (uniform_extension :
      ∀ (S : RepairedControlledSchedulesData.{u})
        (N : RepairedNoncollapseInductionData S)
        (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p),
        ∃ rNext : ℝ, 0 < rNext ∧ rNext ≤ p.r (Fin.last p.i) ∧
          ∃ deltaNext : ℝ, 0 < deltaNext ∧
            deltaNext ≤ (Classical.choice (N.induction p hp)).cutoff rNext ∧
            ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
              SurgeryObservationIsNextEpoch p O →
              SurgeryPrefixControls p F O →
              SurgeryFlowAdmissible F →
              SurgeryFlowPinched F →
              SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
              SurgeryPostPrefixScales p F O rNext deltaNext →
              (∀ t ∈ surgeryObservationInterval O ∩
                Set.Ico (surgeryEpochStart (p.i - 1)) O.H,
                F.parameters.delta t ≤ deltaNext) →
              SurgeryCanonicalOn F (surgeryObservationInterval O) rNext) :
    ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N) := by
  intro S N
  refine ⟨⟨?_⟩⟩
  intro p hp
  obtain ⟨rNext, hr, hrLast, deltaNext, hdelta, hcutoff, hcanonical⟩ :=
    uniform_extension S N p hp
  exact ⟨{
    rNext := rNext
    deltaNext := deltaNext
    r_pos := hr
    r_le_last := hrLast
    delta_pos := hdelta
    delta_le_cutoff := hcutoff
    canonical := hcanonical }⟩




theorem canonicalInductionTheory_of_producers
    (scalar_persistence : M47ScalarPersistencePredecessors.{u} →
      M47LocalScalarPersistenceStatement.{u})
    (component_estimate : M47ComponentAnalyticPredecessors.{u} →
      ∀ C : ℝ, 1 ≤ C → Nonempty (M47ComponentAnalyticBounds.{u} C))
    (positive_blowup : M47PositiveComponentBlowupStatement.{u})
    (canonical_induction : ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N)) :
    RepairedCanonicalInductionTheory.{u} :=
  { local_scalar_persistence := scalar_persistence
    component_analytics := component_estimate
    positive_component_blowup := positive_blowup
    induction := canonical_induction }




theorem canonicalInductionTheory_of_remaining_producers
    (component_estimate : M47ComponentAnalyticPredecessors.{u} →
      ∀ C : ℝ, 1 ≤ C → Nonempty (M47ComponentAnalyticBounds.{u} C))
    (positive_blowup : M47PositiveComponentBlowupStatement.{u})
    (canonical_induction : ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N)) :
    RepairedCanonicalInductionTheory.{u} :=
  canonicalInductionTheory_of_producers PoincareConjecture.M47.localScalarPersistence
    component_estimate positive_blowup canonical_induction




theorem canonicalInductionTheory_of_analytic_and_induction
    (hC : RicciFlowCurvatureTheory.{u})
    (component_estimate : M47ComponentAnalyticPredecessors.{u} →
      ∀ C : ℝ, 1 ≤ C → Nonempty (M47ComponentAnalyticBounds.{u} C))
    (canonical_induction : ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N)) :
    RepairedCanonicalInductionTheory.{u} :=
  canonicalInductionTheory_of_remaining_producers component_estimate
    (PoincareConjecture.M47Positive.positive_component_blowup hC) canonical_induction




theorem canonicalInductionTheory_of_induction
    (P : M47Predecessors.{u})
    (canonical_induction : ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N)) :
    RepairedCanonicalInductionTheory.{u} :=
  canonicalInductionTheory_of_analytic_and_induction P.m04
    (PoincareConjecture.M47.componentAnalyticBounds P) canonical_induction

end PoincareConjecture.Proofs.M47
