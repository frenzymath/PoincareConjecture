import PoincareConjecture.Proofs.M47.SeedClosedHorizonVolume
import PoincareConjecture.Proofs.M47.SeedOldBufferedVolume









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_buffered_firstFailure_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        cutoff ≤ (Classical.choice (N.induction p hp)).cutoff rNext ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          SurgeryObservationIsNextEpoch p O → SurgeryPrefixControls p F O →
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ t ∈ surgeryObservationInterval O ∩
            Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta t ≤ cutoff) →
          ∀ T : ℝ, T ∈ Ico (surgeryEpochStart p.i) O.H →
            SurgeryCanonicalOn F (Ico 0 T) rNext →
            SurgeryVolumeControlOn F (Icc (surgeryEpochStart p.i - 1 / 128) T) k
              (fun _ _ => True) := by
  obtain ⟨kNew, hkNew, later⟩ := exists_seed_closed_firstFailure_volume_constant P S N p hp
  obtain ⟨kOld, hkOld, earlier⟩ := exists_seed_old_buffered_volume_constant P S p hp
  let k := min kNew kOld
  refine ⟨k, lt_min hkNew hkOld, ?_⟩
  intro rNext hr hrLast
  obtain ⟨deltaNew, hdNew, hlastNew, hQ, volumeNew⟩ := later rNext hr hrLast
  obtain ⟨deltaOld, hdOld, _hlastOld, volumeOld⟩ := earlier rNext hr hrLast
  let cutoff := min deltaNew deltaOld
  have hsmallNew : cutoff ≤ deltaNew := min_le_left _ _
  have hsmallOld : cutoff ≤ deltaOld := min_le_right _ _
  refine ⟨cutoff, lt_min hdNew hdOld, hsmallNew.trans hlastNew, hsmallNew.trans hQ, ?_⟩
  intro F O hnext old admissible pinched policy scales overlap T ht past
  have newer := volumeNew F O hnext old admissible pinched policy
    (scales.mono_delta hsmallNew) (fun t h => (overlap t h).trans hsmallNew) T ht past
  intro t htime htF x hx r hradius hepsilon test based curvature
  by_cases htOld : t ≤ surgeryEpochStart p.i
  · have hrEpsilon : r ≤ p.setup.epsilon := by rwa [old.epsilon_eq] at hepsilon
    have hv := volumeOld F O hnext old admissible pinched policy
      (scales.mono_delta hsmallOld)
      (fun s hs => (overlap s ⟨hs.1, hs.2.1, hs.1.2⟩).trans hsmallOld)
      t ⟨htime.1, htOld⟩ x r hradius hrEpsilon test based curvature
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_right kNew kOld) (pow_nonneg hradius.le 3))).trans hv
  · have hv := newer t ⟨(lt_of_not_ge htOld).le, htime.2⟩ htF x hx
      r hradius hepsilon test based curvature
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_left kNew kOld) (pow_nonneg hradius.le 3))).trans hv

end PoincareConjecture.Proofs.M47
