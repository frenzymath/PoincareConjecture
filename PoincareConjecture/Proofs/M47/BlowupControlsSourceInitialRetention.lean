import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialAvoidance
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedChart
import PoincareConjecture.Proofs.M36.NeckCoordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {t : ℝ} (hT : t ∈ F.surgery_times)
  [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)



theorem source_negative_neck_interior_retained
    {y : (F.event t hT).terminal.carrier}
    (hy : y ∈ ((F.event t hT).necks i).neck.region
      (-((F.event t hT).necks i).neck.epsilon⁻¹) 0) :
    (F.event t hT).limit_identify.inverse y ∈ interior (F.event t hT).retained_pre := by
  let E := F.event t hT
  let V := (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0
  let W := E.regular_limit ∩ E.limit_identify.map ⁻¹' V
  have hV : IsOpen V := M36.neck_region_isOpen (E.necks i).neck _ _
  have hW : IsOpen W := E.limit_identify.map_smooth.continuousOn.isOpen_inter_preimage
    E.regular_limit_open hV
  have hsub : W ⊆ E.retained_pre := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := E.neck_negative_retained i hx.2
    have hpeq : p = x := by
      calc
        p = E.limit_identify.inverse (E.limit_identify.map p) :=
          (E.limit_identify.left_inverse (E.retained_pre_subset hp)).symm
        _ = E.limit_identify.inverse (E.limit_identify.map x) :=
          congrArg E.limit_identify.inverse hpx
        _ = x := E.limit_identify.left_inverse hx.1
    exact hpeq ▸ hp
  have hregular : E.limit_identify.inverse y ∈ E.regular_limit := by
    exact E.limit_identify.inverse_image.subset
      (mem_image_of_mem E.limit_identify.inverse (mem_univ y))
  have hmap : E.limit_identify.map (E.limit_identify.inverse y) = y :=
    E.limit_identify.right_inverse (mem_univ y)
  apply interior_maximal hsub hW
  refine ⟨hregular, ?_⟩
  change E.limit_identify.map (E.limit_identify.inverse y) ∈ V
  rwa [hmap]



theorem source_initial_chart_retention {A : ℝ}
    (initial : SurgeryCapInitialComparison F t hT i A)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A)
    (havoid : initial.chart x ∉ ((F.event t hT).caps i).carrier) :
    initial.chart x ∈ interior (F.event t hT).retained_post ∧
      (F.event t hT).retention.inverse (initial.chart x) ∈
        interior (F.event t hT).retained_pre ∧
      (F.event t hT).limit_identify.map
        ((F.event t hT).retention.inverse (initial.chart x)) ∈
        ((F.event t hT).necks i).neck.region
          (-((F.event t hT).necks i).neck.epsilon⁻¹) 0 := by
  let E := F.event t hT
  obtain ⟨eta, _, Q, _, _, hlink⟩ := initial.local_metric_link
  have houtside : Q.map x ∉ closure ((E.local_result i).cap_map ''
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 4)) := by
    intro hcap
    apply havoid
    rw [hlink x hx, ← E.local_cap_image i]
    exact mem_image_of_mem (E.local_embed i) hcap
  have hin : Q.map x ∈ (E.local_result i).collapse ''
      (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0 := by
    rw [← (E.local_result i).cap_exterior]
    exact houtside
  obtain ⟨y, hy, hyQ⟩ := hin
  have hpoint : initial.chart x = E.retention.map (E.limit_identify.inverse y) := by
    calc
      initial.chart x = E.local_embed i (Q.map x) := hlink x hx
      _ = E.local_embed i ((E.local_result i).collapse y) :=
        congrArg (E.local_embed i) hyQ.symm
      _ = E.retention.map (E.limit_identify.inverse y) := E.local_retention i y hy
  have hyint : E.limit_identify.inverse y ∈ interior E.retained_pre :=
    source_negative_neck_interior_retained hT i hy
  have hpre : E.retention.inverse (initial.chart x) = E.limit_identify.inverse y := by
    rw [hpoint]
    exact E.retention.left_inverse (interior_subset hyint)
  have hpost : initial.chart x ∈ interior E.retained_post := by
    rw [hpoint, ← M44.regionEquivalence_image_interior E.retention]
    exact mem_image_of_mem E.retention.map hyint
  refine ⟨hpost, hpre.symm ▸ hyint, ?_⟩
  change E.limit_identify.map (E.retention.inverse (initial.chart x)) ∈ _
  rw [hpre, E.limit_identify.right_inverse (mem_univ y)]
  exact hy

end PoincareConjecture.M47
