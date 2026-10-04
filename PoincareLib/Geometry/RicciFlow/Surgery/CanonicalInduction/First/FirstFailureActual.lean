import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.First.FirstFailureActualLimit
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Standard.CanonicalStandardRecutCover

/-!
# Attainment of the actual first canonical failure

The actual setup-epsilon standard cap cover discharges the exposed
neck case at the same limiting point as the compact slab extraction.
The original extension inputs suffice, including when the infimum is
the old epoch endpoint. MT Lemma 17.2, pp. 395-401;
first-failure-actual-limit.md and canonical-standard-recut-certificate.md.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Proofs.M47

/-- The literal first failure is attained at the infimum of the actual
failure-time set, with its inherited strict-past canonical control.
No standard-cover or geometric closedness input remains. MT Lemma 17.2. -/
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

/-- The original first-failure target follows with only the literal
extension inputs and a cutoff chosen before the flow. MT Lemma 17.2,
pp. 395-401. -/
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

end PoincareMT.Proofs.M47
