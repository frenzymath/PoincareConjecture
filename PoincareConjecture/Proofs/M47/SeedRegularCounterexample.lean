import PoincareConjecture.Proofs.M47.SourceCanonical
import PoincareConjecture.Proofs.M47.SeedSequenceOfInitial










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47



theorem exists_seed_regular_counterexample_sequence
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (hno : ¬ Nonempty (SurgeryCanonicalExtension p (Classical.choice (N.induction p hp)))) :
    ∃ k : ℝ, 0 < k ∧ ∀ c : ℕ → ℝ, (∀ n, 0 < c n) →
      ∃ (n0 : ℕ) (r delta : ℕ → ℝ) (F : ℕ → SurgeryFlowData.{u})
        (O : ∀ n, SurgeryObservation (F n)) (t : ℕ → ℝ)
        (W : ∀ n, M33RegularHistoryWindow (F n))
        (H : ∀ n, M33RegularHistoryData (W n))
        (ht : ∀ n, t n ∈ (H n).generalized.interval)
        (y : ∀ n, ((H n).generalized.slice (t n)).carrier),
      ∃ (hPositive : ∀ n, 0 < ((F n).connection (t n)).scalarCurvature
          ((H n).history.forward (t n) (ht n) (y n)))
        (hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
          ((H n).history.forward (t n) (ht n) (y n))) atTop atTop),
        Tendsto r atTop (𝓝 0) ∧ Tendsto delta atTop (𝓝 0) ∧
        (∀ n, r n = p.r (Fin.last p.i) / ((n + n0 : ℕ) + 1 : ℝ) ∧
          (W n).interval = Icc 0 (t n) ∧
          0 < r n ∧ r n ≤ p.r (Fin.last p.i) ∧
          0 < delta n ∧ delta n ≤ c (n + n0) ∧
          delta n ≤ (Classical.choice (N.induction p hp)).cutoff (r n) ∧
          SurgeryObservationIsNextEpoch p (O n) ∧ SurgeryPrefixControls p (F n) (O n) ∧
          SurgeryFlowAdmissible (F n) ∧ SurgeryFlowPinched (F n) ∧
          SurgeryFlowTerminalPolicyOn (F n) (surgeryObservationInterval (O n)) ∧
          SurgeryPostPrefixScales p (F n) (O n) (r n) (delta n) ∧
          (∀ s ∈ surgeryObservationInterval (O n) ∩
            Ico (surgeryEpochStart (p.i - 1)) (O n).H, (F n).parameters.delta s ≤ delta n) ∧
          t n ∈ Ico (surgeryEpochStart p.i) (O n).H ∧
          t n = sInf (canonicalFailureTimes (F n) (O n) (r n)) ∧
          SurgeryCanonicalOn (F n) (Ico 0 (t n)) (r n) ∧
          (r n)⁻¹ ^ 2 ≤ ((F n).connection (t n)).scalarCurvature
            ((H n).history.forward (t n) (ht n) (y n)) ∧
          ¬ SurgeryCanonicalControl (F n) (t n)
            ((H n).history.forward (t n) (ht n) (y n))
            (F n).parameters.epsilon (F n).parameters.C ∧
          SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i - 1 / 128) (t n)) k
            (fun _ _ => True)) ∧
        let V := regularHistoryBlowupSequence F W H t ht y hPositive hDiverges
        ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ n in atTop,
          ENNReal.ofReal (v / (Real.sqrt (V.scale n)) ^ 3) ≤
            calibratedMetricVolume ((V.flow n).metric (V.base n).1) (V.baseBall n rho) := by
  exact exists_seed_regular_counterexample_sequence_of_initial P S B N p hp
    (fun _theta htheta _v hv _z neck hdisjoint hshort =>
      exists_source_standard_initial_neck_canonical_neighborhood
        P S B p hp htheta hv neck hdisjoint hshort) hno

end PoincareConjecture.Proofs.M47
