import PoincareConjecture.Proofs.M47.FirstFailureActualLimit
import PoincareConjecture.Proofs.M47.CanonicalStandardRecutCover

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

theorem firstFailure_attained_infimum
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ p.r (Fin.last p.i)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryObservationIsNextEpoch p O → SurgeryPrefixControls p F O →
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
        SurgeryPostPrefixScales p F O r delta →
        (∀ t ∈ surgeryObservationInterval O ∩
          Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta t ≤ delta) →
        ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r →
        ∃ t ∈ Ico (surgeryEpochStart p.i) O.H,
          t = sInf (canonicalFailureTimes F O r) ∧
          SurgeryCanonicalOn F (Ico 0 t) r ∧
          ∃ x : (F.slice t).carrier,
            r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
            ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
  exact firstFailure_attained_of_standard_cover P S p hp
    (fun _ hs _ hdistance => standard_tip_locus_setup_cap S hs hdistance) r hr hle

theorem firstFailure_attained
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ p.r (Fin.last p.i)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryObservationIsNextEpoch p O → SurgeryPrefixControls p F O →
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
        SurgeryPostPrefixScales p F O r delta →
        (∀ t ∈ surgeryObservationInterval O ∩
          Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta t ≤ delta) →
        ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r →
        ∃ t ∈ Ico (surgeryEpochStart p.i) O.H,
          SurgeryCanonicalOn F (Ico 0 t) r ∧
          ∃ x : (F.slice t).carrier,
            r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
            ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
  obtain ⟨delta, hdelta, hlast, attain⟩ := firstFailure_attained_infimum P S p hp r hr hle
  refine ⟨delta, hdelta, hlast, ?_⟩
  intro F O hnext old admissible pinched policy scales overlap failure
  obtain ⟨t, ht, _hinf, past, x, hscalar, hbad⟩ :=
    attain F O hnext old admissible pinched policy scales overlap failure
  exact ⟨t, ht, past, x, hscalar, hbad⟩

end PoincareConjecture.Proofs.M47
