import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_ObservedCylinder
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_5_OverlapCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

theorem exists_overlapCapCutoff_with_lowCylinders
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
      (∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
        (inputs : ObservedInputs p rNext cutoff F O),
        OverlapCapControl p O inputs.old A eta theta) ∧
      LowScalarCylinderProducer.{u} p rNext cutoff (smallTestRadius B rNext) := by
  have hApos : 0 < A := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨deltaM44, hdeltaM44, hdeltaLast, hpersistence⟩ :=
    exists_seedCompatibleOverlapCapCutoff S p hp rNext hr hrLast A eta theta
      hApos heta htheta hthetaOne
  let cutoff := min deltaM44 (capScalarCutoff p.setup.epsilon c rNext)
  have hcutoff : 0 < cutoff :=
    lt_min hdeltaM44 (capScalarCutoff_pos p.setup.epsilon_pos hc hr)
  have hM44 : cutoff ≤ deltaM44 := min_le_left _ _
  have hfloor : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext := min_le_right _ _
  have hcontrol (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
      (inputs : ObservedInputs p rNext cutoff F O) :
      OverlapCapControl p O inputs.old A eta theta := by
    let larger := inputs.cutoff_mono hM44
    exact hpersistence F O larger.next_epoch larger.old larger.admissible
      larger.pinched larger.scales larger.canonical larger.overlap
  refine ⟨cutoff, hcutoff, hM44.trans hdeltaLast, hcontrol, ?_⟩
  apply lowScalarCylinderProducer_of_birth_bounds P P44 S p hp hB hBanalytic hc
    hr hrLast hfloor
  intro F O inputs t hT hn ht hstart i
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
  exact hcontrol F O inputs t hT ht hstart i

end PoincareConjecture.Proofs.M46
