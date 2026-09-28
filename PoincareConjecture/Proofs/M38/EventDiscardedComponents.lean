import PoincareConjecture.Proofs.M38.ComponentClosures
import PoincareConjecture.Proofs.M38.RegularClosedSides









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]




theorem event_collar_discarded_inter (i : Fin (F.event T hT).cap_count) :
    (eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) ∩
        (F.event T hT).retained_preᶜ =
      eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
  ext y
  constructor
  · rintro ⟨⟨⟨z, s⟩, hs, rfl⟩, hy⟩
    have hpos : 0 < s := by
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hneg | hzero
      · exact hy (interior_subset (event_collar_negative_retained F T hT i
          ⟨(z, s), ⟨Set.mem_univ _, hs.2.1, hneg⟩, rfl⟩))
      · subst s
        have hf : eventCollarMap F T hT i (z, 0) ∈
            frontier (F.event T hT).retained_pre := by
          rw [(F.event T hT).pre_boundary]
          apply Set.mem_iUnion.mpr
          refine ⟨i, ?_⟩
          rw [← event_collar_central F T hT i]
          exact ⟨(z, 0), by simp, rfl⟩
        rw [(F.event T hT).retained_pre_compact.isClosed.frontier_eq] at hf
        exact hy hf.1
    exact ⟨(z, s), ⟨Set.mem_univ _, hpos, hs.2.2⟩, rfl⟩
  · intro hy
    have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (0 : ℝ) 1 ⊆
        Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
      fun z hz => ⟨hz.1, neg_one_lt_zero.trans hz.2.1, hz.2.2⟩
    refine ⟨Set.image_mono hsub hy, ?_⟩
    exact fun hret => Set.disjoint_left.mp
      (event_collar_positive_discarded F T hT i) hy hret


theorem event_collar_positive_connected (i : Fin (F.event T hT).cap_count) :
    IsConnected (eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) := by
  let : ConnectedSpace UnitTwoSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  apply (isConnected_univ.prod (isConnected_Ioo zero_lt_one)).image
  exact (event_collar_smooth F T hT i).continuousOn.mono
    (fun z hz => ⟨hz.1, neg_one_lt_zero.trans hz.2.1, hz.2.2⟩)



theorem event_discarded_connected_neighborhoods :
    ∀ x ∈ closure (F.event T hT).retained_preᶜ,
      ∃ U : Set (F.slice (F.event T hT).tMinus).carrier,
        IsOpen U ∧ x ∈ U ∧ IsPreconnected (U ∩ (F.event T hT).retained_preᶜ) := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  intro x hx
  by_cases hxo : x ∈ (F.event T hT).retained_preᶜ
  · refine ⟨connectedComponentIn (F.event T hT).retained_preᶜ x,
      (F.event T hT).retained_pre_compact.isClosed.isOpen_compl.connectedComponentIn,
      mem_connectedComponentIn hxo, ?_⟩
    rw [Set.inter_eq_left.mpr (connectedComponentIn_subset _ _)]
    exact isPreconnected_connectedComponentIn
  · have hxr : x ∈ (F.event T hT).retained_pre := by
      simpa only [Set.mem_compl_iff, not_not] using hxo
    have hxi : x ∉ interior (F.event T hT).retained_pre := by
      simpa only [closure_compl, Set.mem_compl_iff] using hx
    have hf : x ∈ frontier (F.event T hT).retained_pre := by
      rw [(F.event T hT).retained_pre_compact.isClosed.frontier_eq]
      exact ⟨hxr, hxi⟩
    rw [(F.event T hT).pre_boundary] at hf
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
    rw [← event_collar_central F T hT i] at hi
    obtain ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩ := hi
    have hs0 : s = 0 := hs
    subst s
    refine ⟨eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1),
      event_collar_open_on F T hT i (isOpen_univ.prod isOpen_Ioo) Set.Subset.rfl,
      ⟨(z, 0), by simp, rfl⟩, ?_⟩
    rw [event_collar_discarded_inter]
    exact (event_collar_positive_connected F T hT i).isPreconnected




theorem event_discarded_component_closure
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hx : x ∈ (F.event T hT).retained_preᶜ) :
    closure (connectedComponentIn (F.event T hT).retained_preᶜ x) =
      connectedComponentIn (interior (F.event T hT).retained_pre)ᶜ x := by
  simpa only [closure_compl] using
    closure_componentIn_eq (event_discarded_connected_neighborhoods F T hT) x hx



theorem exists_event_discarded_component_closure
    (z : (F.slice (F.event T hT).tMinus).carrier)
    (hz : z ∈ (interior (F.event T hT).retained_pre)ᶜ) :
    ∃ x ∈ (F.event T hT).retained_preᶜ,
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x) =
        connectedComponentIn (interior (F.event T hT).retained_pre)ᶜ z := by
  simpa only [closure_compl] using
    exists_component_closure (event_discarded_connected_neighborhoods F T hT) z
      (show z ∈ closure (F.event T hT).retained_preᶜ by rwa [closure_compl])


theorem event_discarded_component_closure_compact
    (x : (F.slice (F.event T hT).tMinus).carrier) :
    IsCompact (closure (connectedComponentIn (F.event T hT).retained_preᶜ x)) := by
  let : CompactSpace (F.slice (F.event T hT).tMinus).carrier :=
    isCompact_univ_iff.mp (F.slices_compact _
      (mem_time_domain_before_surgery F hT (F.event T hT).tMinus_nonnegative
        (F.event T hT).tMinus_lt.le))
  exact isClosed_closure.isCompact

end PoincareConjecture.M38
