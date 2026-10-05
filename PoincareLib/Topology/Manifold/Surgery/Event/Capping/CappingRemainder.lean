import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventCapCoordinates
import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventSlices

/-!
# The compact old remainder in discarded-side capping

Removing half-width collar neighborhoods from the closed discarded side
leaves a compact subset of its open interior. Every old point outside
this remainder is covered by a positive half-width collar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- Half-width neighborhoods of the actual finite surgery spheres. -/
noncomputable def eventCappingNeighborhood : Set (F.slice (F.event T hT).tMinus).carrier :=
  ⋃ i, (P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 / 2 : ℝ) (1 / 2))

/-- The actual collar neighborhoods are open. -/
theorem eventCappingNeighborhood_open : IsOpen (eventCappingNeighborhood F T hT P) := by
  apply isOpen_iUnion
  intro i
  apply (P i).collar_open_on (isOpen_univ.prod isOpen_Ioo)
  intro z hz
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-- The compact remainder is taken on the closed discarded side. -/
noncomputable def eventCappingRemainder : Set (F.slice (F.event T hT).tMinus).carrier :=
  (interior (F.event T hT).retained_pre)ᶜ \ eventCappingNeighborhood F T hT P

/-- Compactness comes from the actual compact pre-slice and the open
removed collar neighborhoods. -/
theorem eventCappingRemainder_compact : IsCompact (eventCappingRemainder F T hT P) := by
  have ht := mem_time_domain_before_surgery F hT (F.event T hT).tMinus_nonnegative
    (F.event T hT).tMinus_lt.le
  letI : CompactSpace (F.slice (F.event T hT).tMinus).carrier :=
    isCompact_univ_iff.mp (F.slices_compact _ ht)
  exact (isOpen_interior.isClosed_compl.inter
    (eventCappingNeighborhood_open F T hT P).isClosed_compl).isCompact

/-- The removed collars contain every boundary sphere, so the remainder
lies entirely in the old open discarded interior. -/
theorem eventCappingRemainder_discarded :
    eventCappingRemainder F T hT P ⊆ (F.event T hT).retained_preᶜ := by
  intro x hx hretained
  have hfront : x ∈ frontier (F.event T hT).retained_pre := by
    rw [(F.event T hT).retained_pre_compact.isClosed.frontier_eq]
    exact ⟨hretained, hx.1⟩
  rw [(F.event T hT).pre_boundary] at hfront
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hfront
  rw [← (P i).collar_central] at hi
  obtain ⟨⟨z, s⟩, ⟨_, hs⟩, hmap⟩ := hi
  have hs0 : s = 0 := hs
  subst s
  apply hx.2
  exact Set.mem_iUnion.mpr ⟨i, (z, 0), ⟨Set.mem_univ _, by norm_num⟩, hmap⟩

/-- Every old discarded point outside the compact remainder lies on an
actual positive half-collar with parameter strictly below one half. -/
theorem eventCappingRemainder_cover {x : (F.slice (F.event T hT).tMinus).carrier}
    (hx : x ∈ (F.event T hT).retained_preᶜ)
    (hnot : x ∉ eventCappingRemainder F T hT P) :
    ∃ i, ∃ z : UnitTwoSphere, ∃ s ∈ Set.Ioo (0 : ℝ) (1 / 2),
      (P i).collar (z, s) = x := by
  have hW : x ∈ eventCappingNeighborhood F T hT P := by
    by_contra hW
    exact hnot ⟨fun h => hx (interior_subset h), hW⟩
  obtain ⟨i, ⟨z, s⟩, ⟨_, hs⟩, hmap⟩ := Set.mem_iUnion.mp hW
  have hpos : 0 < s := by
    rcases lt_trichotomy s 0 with hneg | hzero | hpos
    · exfalso
      apply hx
      rw [← hmap]
      apply interior_subset
      exact (P i).negative_interior ⟨(z, s),
        ⟨Set.mem_univ _, by linarith [hs.1], hneg⟩, rfl⟩
    · exfalso
      apply hx
      rw [← hmap, hzero]
      exact event_cap_collar_central_retained F T hT i (P i).radius_pos
        (P i).width (P i).intrinsic_ball z
    · exact hpos
  exact ⟨i, z, s, ⟨hpos, hs.2⟩, hmap⟩

end PoincareMT.M38
