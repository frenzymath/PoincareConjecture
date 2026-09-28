import PoincareConjecture.Proofs.M47.PositiveHistoryTerminal
import PoincareConjecture.Definitions.Ch15.SurgeryEndPolicy










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive




theorem surgery_positive_component_whole_retention
    (hC : RicciFlowCurvatureTheory.{u}) (F : SurgeryFlowData.{u})
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T : ℝ} (hTJ : T ∈ J) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (v : Ico (F.event T hT).tMinus T)
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hpos : SurgeryPositiveComponentAt F v.1 ((F.event T hT).pre_identify v x))
    {q : (F.slice (F.event T hT).tMinus).carrier}
    (hq : q ∈ connectedComponent x) (hretained : q ∈ (F.event T hT).retained_pre) :
    connectedComponent x ⊆ interior (F.event T hT).retained_pre ∧
      (F.event T hT).retention.map '' connectedComponent x =
        connectedComponent ((F.event T hT).retention.map x) ∧
      ∀ i, Disjoint ((F.event T hT).retention.map '' connectedComponent x)
        ((F.event T hT).caps i).carrier := by
  let E := F.event T hT
  have htm : E.tMinus ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
      ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩
  let : CompactSpace (F.slice E.tMinus).carrier :=
    isCompact_univ_iff.mp (F.slices_compact E.tMinus htm)
  have hstart : ∀ y ∈ connectedComponent x, ∀ u w : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (E.pre_flow.metric v.1) y u w →
        0 < (E.pre_flow.connection v.1).sectionalCurvature y u w :=
    (Proofs.M46.component_positive_iff_of_diffeomorph (E.pre_flow.connection v.1)
      (F.connection v.1) (E.pre_identify v)
      (fun y u w => (E.pre_metric v y u w).symm) x).mpr hpos
  obtain ⟨policy⟩ := hpolicy.nonempty T hTJ hT
  exact positive_pre_component_whole_retention hC E policy v x hstart hq hretained



theorem positive_retained_child_cap_free
    (hC : RicciFlowCurvatureTheory.{u}) (F : SurgeryFlowData.{u})
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T : ℝ} (hTJ : T ∈ J) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (v : Ico (F.event T hT).tMinus T)
    (q : (F.slice (F.event T hT).tMinus).carrier)
    (hretained : q ∈ (F.event T hT).retained_pre)
    (hpos : SurgeryPositiveComponentAt F v.1 ((F.event T hT).pre_identify v q)) :
    ∀ i, Disjoint (connectedComponent ((F.event T hT).retention.map q))
      ((F.event T hT).caps i).carrier := by
  obtain ⟨_, himage, hfree⟩ := surgery_positive_component_whole_retention hC F
    hpolicy hTJ hT v q hpos mem_connectedComponent hretained
  intro i
  simpa only [himage] using hfree i




theorem pre_component_nonpositive_of_retained_child_meets_cap
    (hC : RicciFlowCurvatureTheory.{u}) (F : SurgeryFlowData.{u})
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T : ℝ} (hTJ : T ∈ J) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (v : Ico (F.event T hT).tMinus T)
    (q : (F.slice (F.event T hT).tMinus).carrier)
    (hretained : q ∈ (F.event T hT).retained_pre)
    {i : Fin (F.event T hT).cap_count}
    (hcontact : (connectedComponent ((F.event T hT).retention.map q) ∩
      ((F.event T hT).caps i).carrier).Nonempty) :
    ¬ SurgeryPositiveComponentAt F v.1 ((F.event T hT).pre_identify v q) := by
  intro hpos
  obtain ⟨z, hz, hzcap⟩ := hcontact
  exact Set.disjoint_left.mp (positive_retained_child_cap_free hC F
    hpolicy hTJ hT v q hretained hpos i) hz hzcap

end PoincareConjecture.M47Positive
