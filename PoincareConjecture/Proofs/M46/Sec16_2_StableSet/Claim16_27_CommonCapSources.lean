import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CommonCapCutoff
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_StableSource

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

theorem exists_common_cap_cutoff_with_seed_bounds
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c theta A eta rNext : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hA : S.standard_initial.cylindrical_end.radius + 5 < A) (heta : 0 < eta)
    (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hbound : ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = S.standard_initial)
      (model : MaximalStandardCapFlow F.standard_initial),
      HEq model S.cap_persistence.standard_cap.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A),
      SurgeryCapFamilyComparison F model A eta e initial.chart →
      0 < F.parameters.h t → ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (e.forward s hs (initial.chart x))) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      cutoff ≤ capScalarCutoff p.setup.epsilon c rNext ∧
      (∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
        (inputs : ObservedInputs p rNext cutoff F O),
        OverlapCapControl p O inputs.old A eta theta ∧
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
          t ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ t →
          ∀ i : Fin (F.event t hT).cap_count,
          ∀ x ∈ ((F.event t hT).caps i).carrier,
            c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature x) ∧
      LowScalarCylinderProducer.{u} p rNext cutoff (smallTestRadius B rNext) := by
  obtain ⟨cutoff0, hcutoff0, hlast, hcontrol0, hlow0⟩ :=
    exists_overlapCapCutoff_with_lowCylinders P P44 S p hp hB hBanalytic hc
      htheta hthetaOne hA heta hr hrLast hbound
  let cutoff := min cutoff0 (capScalarCutoff p.setup.epsilon c rNext)
  have hcutoff : 0 < cutoff :=
    lt_min hcutoff0 (capScalarCutoff_pos p.setup.epsilon_pos hc hr)
  have hsmall : cutoff ≤ cutoff0 := min_le_left _ _
  have hfloor : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext := min_le_right _ _
  refine ⟨cutoff, hcutoff, hsmall.trans hlast, hfloor, ?_, hlow0.cutoff_mono hsmall⟩
  intro F O inputs
  have hcontrol : OverlapCapControl p O inputs.old A eta theta :=
    hcontrol0 F O (inputs.cutoff_mono hsmall)
  refine ⟨hcontrol, ?_⟩
  intro t hT hn ht hstart i
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [inputs.old.standard_initial_eq, hp.setup_eq, S.setup_standard_initial_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq (O.redecorateTo inputs.old.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow :=
    (redecorateTo_standard_flow O inputs.old.standard_initial_eq).trans hpflow
  have hAF : F.standard_initial.cylindrical_end.radius + 5 < A := by
    rw [hinitial]
    exact hA
  apply insertedCap_scalarLower_of_persistence
    (O.redecorateTo inputs.old.standard_initial_eq) hT i htheta hAF ht.2
    (fun J U e initial comparison => hbound F hinitial _ hmodel t hT hn i
      J U e initial comparison
        (F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))))
  exact hcontrol t hT ht hstart i

end PoincareConjecture.Proofs.M46
