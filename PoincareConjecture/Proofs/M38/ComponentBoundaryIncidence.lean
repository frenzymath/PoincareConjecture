import PoincareConjecture.Proofs.M38.ComponentFrontiers
import PoincareConjecture.Proofs.M38.EventDiscardedComponents
import PoincareConjecture.Proofs.M38.CappingComponentLabels










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier]

namespace EventCapCoordinates

variable {i : Fin (F.event T hT).cap_count} (P : EventCapCoordinates F T hT i)


theorem attachmentChart_target_image :
  Subtype.val '' P.attachmentChart.target =
      P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
  rw [P.attachmentChart_target]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, P.annular_target_discarded hy⟩, hy, rfl⟩


theorem positive_collar_connected :
    IsConnected (P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) := by
  rw [← P.attachmentChart_target_image]
  exact P.attachmentChart_target_connected.image _ continuous_subtype_val.continuousOn


theorem attachmentPoint_positive :
    P.attachmentPoint.val ∈ P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
  have h := P.attachmentPoint_mem
  rwa [P.attachmentChart_target] at h



theorem collar_discarded_inter :
    (P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) ∩
        (F.event T hT).retained_preᶜ =
      P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
  ext y
  constructor
  · rintro ⟨⟨⟨z, s⟩, hs, rfl⟩, hy⟩
    have hpos : 0 < s := by
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hneg | hzero
      · exact hy (interior_subset (P.negative_interior
          ⟨(z, s), ⟨Set.mem_univ _, hs.2.1, hneg⟩, rfl⟩))
      · subst s
        have hf : P.collar (z, 0) ∈ frontier (F.event T hT).retained_pre := by
          rw [(F.event T hT).pre_boundary]
          apply Set.mem_iUnion.mpr
          refine ⟨i, ?_⟩
          rw [← P.collar_central]
          exact ⟨(z, 0), by simp, rfl⟩
        exact hy ((F.event T hT).retained_pre_compact.isClosed.frontier_subset hf)
    exact ⟨(z, s), ⟨Set.mem_univ _, hpos, hs.2.2⟩, rfl⟩
  · intro hy
    have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (0 : ℝ) 1 ⊆
        Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
      fun z hz => ⟨hz.1, neg_one_lt_zero.trans hz.2.1, hz.2.2⟩
    exact ⟨Set.image_mono hsub hy, P.annular_target_discarded hy⟩



theorem central_mem_closure_positive (z : UnitTwoSphere) :
    P.collar (z, 0) ∈ closure (P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) := by
  let V : Set RoundCylinderSpace := Set.univ ×ˢ Set.Ioo (0 : ℝ) (1 / 2)
  have hclosure : closure V = Set.univ ×ˢ Set.Icc (0 : ℝ) (1 / 2) := by
    dsimp only [V]
    rw [closure_prod_eq, closure_univ, closure_Ioo (by norm_num)]
  have hsub : closure V ⊆ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    rw [hclosure]
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hzero : (z, 0) ∈ closure V := by
    rw [hclosure]
    exact ⟨Set.mem_univ z, le_rfl, by norm_num⟩
  have himage : P.collar (z, 0) ∈ closure (P.collar '' V) :=
    (P.collarChart.continuousOn_toFun.mono hsub).image_closure
      (Set.mem_image_of_mem _ hzero)
  apply closure_mono (Set.image_mono ?_) himage
  intro p hp
  exact ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩


theorem positive_collar_subset_component (x : eventDiscardedOpen F T hT)
    (hlabel : ConnectedComponents.mk P.attachmentPoint = ConnectedComponents.mk x) :
    P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) ⊆
      connectedComponentIn (F.event T hT).retained_preᶜ x.val := by
  rw [← P.attachmentChart_target_image, connectedComponentIn_eq_image
    (show x.val ∈ (F.event T hT).retained_preᶜ from x.property)]
  apply Set.image_mono
  intro y hy
  exact ConnectedComponents.coe_eq_coe'.mp ((P.attachment_component_eq hy).trans hlabel)



theorem central_mem_component_closure_iff (x : eventDiscardedOpen F T hT)
    (z : UnitTwoSphere) :
    P.collar (z, 0) ∈ closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ↔
      ConnectedComponents.mk P.attachmentPoint = ConnectedComponents.mk x := by
  constructor
  · intro hz
    let U := P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
    have hU : IsOpen U := P.collarChart.open_target
    have hzU : P.collar (z, 0) ∈ U := ⟨(z, 0), by simp, rfl⟩
    have hconnected : IsPreconnected (U ∩ (F.event T hT).retained_preᶜ) := by
      rw [P.collar_discarded_inter]
      exact P.positive_collar_connected.isPreconnected
    have hsub := local_inter_subset_component hconnected
      (mem_closure_iff.mp hz U hU hzU)
    have hx : P.attachmentPoint.val ∈
        connectedComponentIn (F.event T hT).retained_preᶜ x.val := by
      apply hsub
      rw [P.collar_discarded_inter]
      exact P.attachmentPoint_positive
    rw [connectedComponentIn_eq_image
      (show x.val ∈ (F.event T hT).retained_preᶜ from x.property)] at hx
    obtain ⟨y, hy, heq⟩ := hx
    have heq' : y = P.attachmentPoint := Subtype.ext heq
    rw [heq'] at hy
    exact ConnectedComponents.coe_eq_coe'.mpr hy
  · intro hlabel
    exact closure_mono (P.positive_collar_subset_component x hlabel)
      (P.central_mem_closure_positive z)

end EventCapCoordinates

variable (F T hT) (P : ∀ i, EventCapCoordinates F T hT i)




theorem event_component_frontier (x : eventDiscardedOpen F T hT) :
    frontier (connectedComponentIn (F.event T hT).retained_preᶜ x.val) =
      ⋃ i : {i : Fin (F.event T hT).cap_count //
          ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x},
        (F.event T hT).limit_identify.inverse ''
          ((F.event T hT).necks i.val).neck.central_sphere := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  have hO := (F.event T hT).retained_pre_compact.isClosed.isOpen_compl
  ext y
  constructor
  · intro hy
    have hf := componentIn_frontier_subset hO x.property hy
    rw [frontier_compl, (F.event T hT).pre_boundary] at hf
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
    have hlabel : ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x := by
      rw [← (P i).collar_central] at hi
      obtain ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩ := hi
      have hs0 : s = 0 := hs
      subst s
      exact ((P i).central_mem_component_closure_iff x z).mp (frontier_subset_closure hy)
    exact Set.mem_iUnion.mpr ⟨⟨i, hlabel⟩, hi⟩
  · intro hy
    obtain ⟨⟨i, hi⟩, hy⟩ := Set.mem_iUnion.mp hy
    have hret : y ∈ (F.event T hT).retained_pre := by
      apply (F.event T hT).retained_pre_compact.isClosed.frontier_subset
      rw [(F.event T hT).pre_boundary]
      exact Set.mem_iUnion.mpr ⟨i, hy⟩
    rw [hO.connectedComponentIn.frontier_eq]
    refine ⟨?_, fun hyC => connectedComponentIn_subset _ _ hyC hret⟩
    rw [← (P i).collar_central] at hy
    obtain ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩ := hy
    have hs0 : s = 0 := hs
    subst s
    exact ((P i).central_mem_component_closure_iff x z).mpr hi



theorem event_component_interior_closure (x : eventDiscardedOpen F T hT) :
    interior (closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val)) =
      connectedComponentIn (F.event T hT).retained_preᶜ x.val := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  apply componentIn_interior_closure
    (F.event T hT).retained_pre_compact.isClosed.isOpen_compl x.property
  rw [closure_compl, event_discarded_interior]



theorem event_closed_component_frontier (x : eventDiscardedOpen F T hT) :
    frontier (closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val)) =
      ⋃ i : {i : Fin (F.event T hT).cap_count //
          ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x},
        (F.event T hT).limit_identify.inverse ''
          ((F.event T hT).necks i.val).neck.central_sphere := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  rw [componentIn_frontier_closure
    (F.event T hT).retained_pre_compact.isClosed.isOpen_compl x.property
      (by rw [closure_compl, event_discarded_interior])]
  exact event_component_frontier F T hT P x



theorem event_component_frontier_nonempty_iff (x : eventDiscardedOpen F T hT) :
    (frontier (connectedComponentIn (F.event T hT).retained_preᶜ x.val)).Nonempty ↔
      ∃ i, ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x := by
  rw [event_component_frontier F T hT P x]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hy
    exact ⟨i.val, i.property⟩
  · rintro ⟨i, hi⟩
    obtain ⟨y, hy⟩ := (event_sphere_connected F T hT i).nonempty
    exact ⟨y, Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hy⟩⟩



theorem event_component_boundary_unique (x : eventDiscardedOpen F T hT)
    (y : (F.slice (F.event T hT).tMinus).carrier)
    (hy : y ∈ frontier (connectedComponentIn (F.event T hT).retained_preᶜ x.val)) :
    ∃! i : Fin (F.event T hT).cap_count,
      ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x ∧
        y ∈ (F.event T hT).limit_identify.inverse ''
          ((F.event T hT).necks i).neck.central_sphere := by
  rw [event_component_frontier F T hT P x] at hy
  obtain ⟨⟨i, hi⟩, hyi⟩ := Set.mem_iUnion.mp hy
  refine ⟨i, ⟨hi, hyi⟩, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (event_spheres_disjoint F T hT j i hji) hj.2 hyi

end PoincareConjecture.M38
