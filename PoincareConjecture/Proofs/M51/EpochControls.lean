import PoincareConjecture.Proofs.M51.ObservationControls
import PoincareConjecture.Proofs.M51.EpochProfiles
import PoincareConjecture.Proofs.M47.CanonicalControls

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M51Numerical

variable (S : RepairedControlledSchedulesData.{u})
  (N : RepairedNoncollapseInductionData S) (C : RepairedCanonicalInductionData S N)

theorem continuationControls (n : ℕ) (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (delta : ℝ → ℝ)
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j)
    (old : SurgeryPrefixControls (prefixAt S N C n) F O)
    (hpinched : SurgeryFlowPinched F)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (hstart : surgeryEpochStart (prefixAt S N C n).i ≤ O.H)
    (hend : O.H ≤ surgeryEpochStart ((prefixAt S N C n).i + 1)) :
    SurgeryEpochContinuationControls (prefixAt S N C n) F O
      (noncollapse S N C n) (canonical S N C n) ∧
    SurgeryNoncollapsedOn F (surgeryObservationInterval O)
      (noncollapse S N C n).kappaNew := by
  obtain ⟨hr, hk, hh, hd⟩ := stepProfiles S N C n F delta hdelta hprofiles hcut
  by_cases hstrict : surgeryEpochStart (prefixAt S N C n).i < O.H
  · have hnext : SurgeryObservationIsNextEpoch (prefixAt S N C n) O := ⟨hstrict, hend⟩
    have hepoch {t : ℝ}
        (ht : t ∈ surgeryObservationInterval O ∩ Ici (surgeryEpochStart (prefixAt S N C n).i)) :
        t ∈ surgeryEpoch (prefixAt S N C n).i := ⟨ht.2, ht.1.2.trans_le hend⟩
    have hoverlap {t : ℝ} (ht : t ∈ surgeryEpoch (prefixAt S N C n).i) :
        t ∈ overlapInterval (prefixAt S N C n) :=
      ⟨(epochStart_strictMono.monotone (Nat.sub_le _ 1)).trans ht.1, ht.2⟩
    have scales : SurgeryPostPrefixScales (prefixAt S N C n) F O
        (canonical S N C n).rNext (canonical S N C n).deltaNext := {
      r_eq := fun t ht => hr t (hepoch ht)
      delta_le := fun t ht => hd t (hoverlap (hepoch ht))
      h_eq := fun t ht => hh t (hepoch ht) }
    have overlap : ∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart ((prefixAt S N C n).i - 1)) O.H,
        F.parameters.delta t ≤ (canonical S N C n).deltaNext :=
      fun t ht => hd t ⟨ht.2.1, ht.1.2.trans_le hend⟩
    obtain ⟨hcanonical, hnoncollapsed⟩ := (canonical S N C n).observedControls
      F O hnext old old.admissible hpinched terminal_policy scales overlap
    exact ⟨⟨hcanonical, old.noncollapsedAssumptionOn hnext hnoncollapsed hk,
      hr, hk, hh, hd⟩, hnoncollapsed⟩
  · have hboundary : O.H = surgeryEpochStart (prefixAt S N C n).i :=
      le_antisymm (le_of_not_gt hstrict) hstart
    exact ⟨⟨old.canonicalBeforePrefix hboundary.le (canonical S N C n),
      old.noncollapsedProfileBeforePrefix hboundary.le, hr, hk, hh, hd⟩,
      old.noncollapsedBeforePrefix hboundary.le (noncollapse S N C n)⟩

end PoincareConjecture.M51Numerical
