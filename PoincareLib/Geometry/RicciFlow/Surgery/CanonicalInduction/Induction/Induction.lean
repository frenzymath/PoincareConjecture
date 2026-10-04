import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Scalar.ScalarPersistenceProof
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Positive.PositiveGradientTerminal
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Component.ComponentEstimateProof

/-!
# Proposition 17.1: assembly interfaces

Morgan--Tian Proposition 17.1 and Lemma 17.2, pp. 395-396. These logical
consumers keep the four actual output types and the uniform choice of the
next radius and cutoff explicit. Their producer arguments remain proof
obligations; this module does not prove first-failure attainment, positive
component volume, or the blow-up contradiction.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.Proofs.M47

/-- Lemma 17.2, pp. 395-396: an attained first failure is incompatible with
the canonical conclusion constructed at that same time and point. -/
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

/-- Package the uniform constants of Proposition 17.1, p. 395. The geometric
producer selects the radius and then the cutoff before every candidate flow;
the extension is indexed by the exact choice made by the supplied M46 data. -/
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

/-- Assemble the four literal M47 outputs once their producers are proved.
Sources: MT equation (3.7), p. 41; Theorem 4.23, pp. 74-75; and Proposition
17.1, pp. 395-409. No producer is supplied by this packaging theorem. -/
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

/-- Substitute the proved local scalar-persistence output into the literal
four-field interface. The remaining producer types are unchanged; MT
equation (3.7), p. 41, and Proposition 17.1, pp. 395-409. -/
theorem canonicalInductionTheory_of_remaining_producers
    (component_estimate : M47ComponentAnalyticPredecessors.{u} →
      ∀ C : ℝ, 1 ≤ C → Nonempty (M47ComponentAnalyticBounds.{u} C))
    (positive_blowup : M47PositiveComponentBlowupStatement.{u})
    (canonical_induction : ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N)) :
    RepairedCanonicalInductionTheory.{u} :=
  canonicalInductionTheory_of_producers PoincareMT.M47.localScalarPersistence
    component_estimate positive_blowup canonical_induction

/-- Substitute both completed supporting outputs. The curvature theory is
the existing M04 predecessor; the two remaining producer statements retain
their literal types, Theorem 4.23 and Proposition 17.1, pp. 74-75, 395-409. -/
theorem canonicalInductionTheory_of_analytic_and_induction
    (hC : RicciFlowCurvatureTheory.{u})
    (component_estimate : M47ComponentAnalyticPredecessors.{u} →
      ∀ C : ℝ, 1 ≤ C → Nonempty (M47ComponentAnalyticBounds.{u} C))
    (canonical_induction : ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N)) :
    RepairedCanonicalInductionTheory.{u} :=
  canonicalInductionTheory_of_remaining_producers component_estimate
    (PoincareMT.M47Positive.positive_component_blowup hC) canonical_induction

/-- All three supporting outputs are now proved and substituted at their
literal field types. Only the actual canonical-induction producer remains;
Theorem 4.23 and Proposition 17.1, pp. 74-75 and 395-409. -/
theorem canonicalInductionTheory_of_induction
    (P : M47Predecessors.{u})
    (canonical_induction : ∀ (S : RepairedControlledSchedulesData.{u})
      (N : RepairedNoncollapseInductionData S),
      Nonempty (RepairedCanonicalInductionData S N)) :
    RepairedCanonicalInductionTheory.{u} :=
  canonicalInductionTheory_of_analytic_and_induction P.m04
    (PoincareMT.M47.componentAnalyticBounds P) canonical_induction

end PoincareMT.Proofs.M47
