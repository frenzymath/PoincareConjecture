import PoincareConjecture.Proofs.M38.RetainedComponents
import PoincareConjecture.Proofs.M38.ComponentBoundaryIncidence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier]

namespace EventCapCoordinates

variable {i : Fin (F.event T hT).cap_count} (P : EventCapCoordinates F T hT i)


noncomputable def retainedAttachmentPoint : eventRetainedInteriorOpen F T hT :=
  ⟨P.collar (capUnitDirection (0 : StandardCapSpace), -(1 / 2)),
    P.negative_interior ⟨(capUnitDirection (0 : StandardCapSpace), -(1 / 2)),
      by norm_num, rfl⟩⟩


theorem retainedAttachmentPoint_negative : P.retainedAttachmentPoint.val ∈
    P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) :=
  ⟨(capUnitDirection (0 : StandardCapSpace), -(1 / 2)), by norm_num, rfl⟩



theorem retainedAttachmentPoint_image :
    (F.event T hT).retention.map P.retainedAttachmentPoint.val =
      P.retainedAnnularPoint.val := by
  change (F.event T hT).retention.map
    (P.collar (capUnitDirection (0 : StandardCapSpace), -(1 / 2))) =
      P.ball.map capAnnularPoint.val
  rw [← P.retained_gluing (capUnitDirection (0 : StandardCapSpace)) (-(1 / 2)) (by norm_num)]
  change P.ball.map ((1 - -(1 / 2)) • (capUnitDirection (0 : StandardCapSpace)).val) =
    P.ball.map ((3 / 2 : ℝ) • (capUnitDirection (0 : StandardCapSpace)).val)
  norm_num


theorem negative_collar_connected :
    IsConnected (P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0)) := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  apply (isConnected_univ.prod (isConnected_Ioo neg_one_lt_zero)).image
  exact P.collarChart.continuousOn_toFun.mono
    (fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans zero_lt_one⟩)



theorem collar_retained_inter :
    (P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) ∩
        interior (F.event T hT).retained_pre =
      P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) := by
  ext y
  constructor
  · rintro ⟨⟨⟨z, s⟩, hs, rfl⟩, hy⟩
    have hneg : s < 0 := by
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hpos | hzero
      · exact P.annular_target_discarded
          ⟨(z, s), ⟨Set.mem_univ _, hpos, hs.2.2⟩, rfl⟩ (interior_subset hy)
      · have hs0 : s = 0 := hzero.symm
        subst s
        have hf : P.collar (z, 0) ∈ frontier (F.event T hT).retained_pre := by
          rw [(F.event T hT).pre_boundary]
          refine Set.mem_iUnion.mpr ⟨i, ?_⟩
          rw [← P.collar_central]
          exact ⟨(z, 0), by simp, rfl⟩
        exact hf.2 hy
    exact ⟨(z, s), ⟨Set.mem_univ _, hs.2.1, hneg⟩, rfl⟩
  · intro hy
    have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (-1 : ℝ) 0 ⊆
        Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
      fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans zero_lt_one⟩
    exact ⟨Set.image_mono hsub hy, P.negative_interior hy⟩



theorem central_mem_closure_negative (z : UnitTwoSphere) :
    P.collar (z, 0) ∈ closure (P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0)) := by
  let V : Set RoundCylinderSpace := Set.univ ×ˢ Set.Ioo (-(1 / 2) : ℝ) 0
  have hclosure : closure V = Set.univ ×ˢ Set.Icc (-(1 / 2) : ℝ) 0 := by
    dsimp only [V]
    rw [closure_prod_eq, closure_univ, closure_Ioo (by norm_num)]
  have hsub : closure V ⊆ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    rw [hclosure]
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hzero : (z, 0) ∈ closure V := by
    rw [hclosure]
    exact ⟨Set.mem_univ z, by norm_num, le_rfl⟩
  have himage : P.collar (z, 0) ∈ closure (P.collar '' V) :=
    (P.collarChart.continuousOn_toFun.mono hsub).image_closure
      (Set.mem_image_of_mem _ hzero)
  apply closure_mono (Set.image_mono ?_) himage
  intro p hp
  exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩



theorem negative_collar_subset_retained_component (x : eventRetainedInteriorOpen F T hT)
    (hlabel : ConnectedComponents.mk P.retainedAttachmentPoint = ConnectedComponents.mk x) :
    P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) ⊆
      connectedComponentIn (interior (F.event T hT).retained_pre) x.val := by
  have hp : P.retainedAttachmentPoint.val ∈
      connectedComponentIn (interior (F.event T hT).retained_pre) x.val := by
    rw [connectedComponentIn_eq_image
      (show x.val ∈ interior (F.event T hT).retained_pre from x.property)]
    exact ⟨P.retainedAttachmentPoint, ConnectedComponents.coe_eq_coe'.mp hlabel, rfl⟩
  rw [connectedComponentIn_eq hp]
  exact P.negative_collar_connected.isPreconnected.subset_connectedComponentIn
    P.retainedAttachmentPoint_negative P.negative_interior



theorem central_mem_retained_component_closure_iff
    (x : eventRetainedInteriorOpen F T hT) (z : UnitTwoSphere) :
    P.collar (z, 0) ∈ closure
        (connectedComponentIn (interior (F.event T hT).retained_pre) x.val) ↔
      ConnectedComponents.mk P.retainedAttachmentPoint = ConnectedComponents.mk x := by
  constructor
  · intro hz
    let U := P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
    have hU : IsOpen U := P.collarChart.open_target
    have hzU : P.collar (z, 0) ∈ U := ⟨(z, 0), by simp, rfl⟩
    have hconnected : IsPreconnected (U ∩ interior (F.event T hT).retained_pre) := by
      rw [P.collar_retained_inter]
      exact P.negative_collar_connected.isPreconnected
    have hsub := local_inter_subset_component hconnected
      (mem_closure_iff.mp hz U hU hzU)
    have hx : P.retainedAttachmentPoint.val ∈
        connectedComponentIn (interior (F.event T hT).retained_pre) x.val := by
      apply hsub
      rw [P.collar_retained_inter]
      exact P.retainedAttachmentPoint_negative
    rw [connectedComponentIn_eq_image
      (show x.val ∈ interior (F.event T hT).retained_pre from x.property)] at hx
    obtain ⟨y, hy, heq⟩ := hx
    have heq' : y = P.retainedAttachmentPoint := Subtype.ext heq
    rw [heq'] at hy
    exact ConnectedComponents.coe_eq_coe'.mpr hy
  · intro hlabel
    exact closure_mono (P.negative_collar_subset_retained_component x hlabel)
      (P.central_mem_closure_negative z)

end EventCapCoordinates

variable (F T hT) (P : ∀ i, EventCapCoordinates F T hT i)




theorem event_retained_component_frontier (x : eventRetainedInteriorOpen F T hT) :
    frontier (connectedComponentIn (interior (F.event T hT).retained_pre) x.val) =
      ⋃ i : {i : Fin (F.event T hT).cap_count //
          ConnectedComponents.mk (P i).retainedAttachmentPoint = ConnectedComponents.mk x},
        (F.event T hT).limit_identify.inverse ''
          ((F.event T hT).necks i.val).neck.central_sphere := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  have hfront : frontier (interior (F.event T hT).retained_pre) =
      frontier (F.event T hT).retained_pre := by
    rw [frontier, event_retained_closure_interior, interior_interior,
      (F.event T hT).retained_pre_compact.isClosed.frontier_eq]
  ext y
  constructor
  · intro hy
    have hf := componentIn_frontier_subset isOpen_interior x.property hy
    rw [hfront, (F.event T hT).pre_boundary] at hf
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
    have hlabel : ConnectedComponents.mk (P i).retainedAttachmentPoint =
        ConnectedComponents.mk x := by
      rw [← (P i).collar_central] at hi
      obtain ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩ := hi
      have hs0 : s = 0 := hs
      subst s
      exact ((P i).central_mem_retained_component_closure_iff x z).mp (frontier_subset_closure hy)
    exact Set.mem_iUnion.mpr ⟨⟨i, hlabel⟩, hi⟩
  · intro hy
    obtain ⟨⟨i, hi⟩, hy⟩ := Set.mem_iUnion.mp hy
    have hnot : y ∉ interior (F.event T hT).retained_pre := by
      have hf : y ∈ frontier (F.event T hT).retained_pre := by
        rw [(F.event T hT).pre_boundary]
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
      exact hf.2
    rw [isOpen_interior.connectedComponentIn.frontier_eq]
    refine ⟨?_, fun hyC => hnot (connectedComponentIn_subset _ _ hyC)⟩
    rw [← (P i).collar_central] at hy
    obtain ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩ := hy
    have hs0 : s = 0 := hs
    subst s
    exact ((P i).central_mem_retained_component_closure_iff x z).mpr hi


theorem event_retained_component_interior_closure (x : eventRetainedInteriorOpen F T hT) :
    interior (closure (connectedComponentIn (interior (F.event T hT).retained_pre) x.val)) =
      connectedComponentIn (interior (F.event T hT).retained_pre) x.val := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  apply componentIn_interior_closure isOpen_interior x.property
  rw [event_retained_closure_interior]



theorem event_retained_closed_component_frontier (x : eventRetainedInteriorOpen F T hT) :
    frontier (closure (connectedComponentIn (interior (F.event T hT).retained_pre) x.val)) =
      ⋃ i : {i : Fin (F.event T hT).cap_count //
          ConnectedComponents.mk (P i).retainedAttachmentPoint = ConnectedComponents.mk x},
        (F.event T hT).limit_identify.inverse ''
          ((F.event T hT).necks i.val).neck.central_sphere := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  rw [componentIn_frontier_closure isOpen_interior x.property
    (by rw [event_retained_closure_interior])]
  exact event_retained_component_frontier F T hT P x



theorem event_retained_component_boundary_unique (x : eventRetainedInteriorOpen F T hT)
    (y : (F.slice (F.event T hT).tMinus).carrier)
    (hy : y ∈ frontier (connectedComponentIn (interior (F.event T hT).retained_pre) x.val)) :
    ∃! i : Fin (F.event T hT).cap_count,
      ConnectedComponents.mk (P i).retainedAttachmentPoint = ConnectedComponents.mk x ∧
        y ∈ (F.event T hT).limit_identify.inverse ''
          ((F.event T hT).necks i).neck.central_sphere := by
  rw [event_retained_component_frontier F T hT P x] at hy
  obtain ⟨⟨i, hi⟩, hyi⟩ := Set.mem_iUnion.mp hy
  refine ⟨i, ⟨hi, hyi⟩, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (event_spheres_disjoint F T hT j i hji) hj.2 hyi

end PoincareConjecture.M38
