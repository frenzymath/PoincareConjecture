import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.First.SeedFirstFailureObservation
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Terminal.SeedTerminalVolume
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Noncollapse.NoncollapseHorizon

/-!
# Uniform tested volume through a strict new-epoch first failure

The density is selected before the next radius and its cutoff. The
canonical strict past supplies the actual restricted observation; the
checked horizon theorem retains the same density at the included endpoint.
Source: MT pp. 393-402; seed-first-failure-horizon.md.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Proofs.M47

/-- Uniform unconditional volume on the closed new-epoch interval before
a first failure strictly later than the old endpoint. Canonical control
at that first-failure time is not supplied. -/
theorem exists_seed_firstFailure_volume_constant
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
          ∀ T : ℝ, T ∈ Ioo (surgeryEpochStart p.i) O.H →
            SurgeryCanonicalOn F (Ico 0 T) rNext →
            SurgeryVolumeControlOn F (Icc (surgeryEpochStart p.i) T) k
              (fun _ _ => True) := by
  obtain ⟨k, hk, produce⟩ := exists_seed_terminal_volume_constant P S N p hp
  refine ⟨k, hk, ?_⟩
  intro rNext hr hrLast
  obtain ⟨cutoff, hcutoff, hlast, hQ, volume⟩ := produce rNext hr hrLast
  refine ⟨cutoff, hcutoff, hlast, hQ, ?_⟩
  intro F O hnext old admissible pinched policy scales overlap T ht past
  have hT : 0 < T := (by
    unfold surgeryEpochStart
    positivity : 0 < surgeryEpochStart p.i).trans ht.1
  have inputs := seed_firstFailure_observedInputs hT ht.2.le ht.1 hnext old
    admissible pinched policy scales overlap past
  apply surgeryVolumeControlOn_closed_horizon P ht.1
  intro t htime _htF x _hcenter r hpositive hepsilon test hbased hcurv
  have hradius : r ≤ p.setup.epsilon := by rwa [old.epsilon_eq] at hepsilon
  exact volume F (O.restrictTo T hT ht.2.le) inputs t htime x r hpositive hradius
    test hbased hcurv

end PoincareMT.Proofs.M47
