import PoincareConjecture.Proofs.M38.CutAnnuli
import PoincareConjecture.Proofs.M38.EventSlices








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))


noncomputable def eventCutSpheres : Set (F.slice (F.event T hT).tMinus).carrier :=
  ⋃ i : S, (P i.val).collar '' (Set.univ ×ˢ ({0} : Set ℝ))


theorem eventCutSpheres_compact : IsCompact (eventCutSpheres F T hT P S) := by
  apply isCompact_iUnion
  intro i
  rw [(P i.val).collar_central]
  exact event_sphere_compact F T hT i.val


noncomputable def eventCutOpen :
    TopologicalSpace.Opens (F.slice (F.event T hT).tMinus).carrier :=
  ⟨(eventCutSpheres F T hT P S)ᶜ, (eventCutSpheres_compact F T hT P S).isClosed.isOpen_compl⟩


theorem cutAnnularChart_target_cutOpen (i : Fin (F.event T hT).cap_count) (positive : Bool) :
    ((P i).cutAnnularChart positive).target ⊆ eventCutOpen F T hT P S := by
  intro x hx hbad
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hbad
  by_cases hij : i = j.val
  · exact Set.disjoint_left.mp ((P i).cutAnnularChart_central_disjoint positive)
      hx (hij.symm ▸ hj)
  · apply Set.disjoint_left.mp ((P i).collars_disjoint (P j.val) hij)
      ((P i).cutAnnularChart_target_subset positive hx)
    apply Set.image_mono _ hj
    intro z hz
    exact ⟨hz.1, by simpa only [Set.mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)⟩


theorem eventCutOpen_nonempty (i : Fin (F.event T hT).cap_count) (positive : Bool) :
    Nonempty (eventCutOpen F T hT P S) := by
  refine ⟨⟨(P i).collar (cutSideReflection positive (capUnitDirection 0, 1 / 2)), ?_⟩⟩
  exact cutAnnularChart_target_cutOpen F T hT P S i positive
    ⟨(capUnitDirection 0, 1 / 2), ⟨Set.mem_univ _, by norm_num⟩, rfl⟩


theorem eventCutOpen_empty :
    (eventCutOpen F T hT P ∅ : Set (F.slice (F.event T hT).tMinus).carrier) = Set.univ := by
  simp [eventCutOpen, eventCutSpheres]


theorem eventCutSpheres_univ :
    eventCutSpheres F T hT P Set.univ = frontier (F.event T hT).retained_pre := by
  rw [(F.event T hT).pre_boundary]
  ext x
  simp only [eventCutSpheres, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, (P i.val).collar_central ▸ hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨i, Set.mem_univ i⟩, (P i).collar_central.symm ▸ hi⟩


theorem eventCutOpen_univ :
    (eventCutOpen F T hT P Set.univ : Set (F.slice (F.event T hT).tMinus).carrier) =
      interior (F.event T hT).retained_pre ∪ (F.event T hT).retained_preᶜ := by
  change (eventCutSpheres F T hT P Set.univ)ᶜ = _
  rw [eventCutSpheres_univ, (F.event T hT).retained_pre_compact.isClosed.frontier_eq]
  ext x
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]
  tauto


theorem cutAnnularChart_targets_disjoint
    (a b : S × Bool) (hab : a ≠ b) :
    Disjoint ((P a.1.val).cutAnnularChart a.2).target
      ((P b.1.val).cutAnnularChart b.2).target := by
  by_cases hij : a.1.val = b.1.val
  · have heq : a.1 = b.1 := Subtype.ext hij
    have hsign : a.2 ≠ b.2 := fun h => hab (Prod.ext heq h)
    rw [hij]
    rcases a with ⟨i, pa⟩
    rcases b with ⟨j, pb⟩
    cases pa <;> cases pb
    · exact (hsign rfl).elim
    · exact (P j.val).cutAnnularChart_opposite_disjoint
    · exact (P j.val).cutAnnularChart_opposite_disjoint.symm
    · exact (hsign rfl).elim
  · exact ((P a.1.val).collars_disjoint (P b.1.val) hij).mono
      ((P a.1.val).cutAnnularChart_target_subset a.2)
      ((P b.1.val).cutAnnularChart_target_subset b.2)


noncomputable def eventCutNeighborhood : Set (F.slice (F.event T hT).tMinus).carrier :=
  ⋃ i : S, (P i.val).collar '' (Set.univ ×ˢ Set.Ioo (-1 / 2 : ℝ) (1 / 2))


theorem eventCutNeighborhood_open : IsOpen (eventCutNeighborhood F T hT P S) := by
  apply isOpen_iUnion
  intro i
  apply (P i.val).collar_open_on (isOpen_univ.prod isOpen_Ioo)
  intro z hz
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩


noncomputable def eventCutRemainder : Set (F.slice (F.event T hT).tMinus).carrier :=
  (eventCutNeighborhood F T hT P S)ᶜ


theorem eventCutRemainder_compact : IsCompact (eventCutRemainder F T hT P S) := by
  have ht := mem_time_domain_before_surgery F hT (F.event T hT).tMinus_nonnegative
    (F.event T hT).tMinus_lt.le
  letI : CompactSpace (F.slice (F.event T hT).tMinus).carrier :=
    isCompact_univ_iff.mp (F.slices_compact _ ht)
  exact (eventCutNeighborhood_open F T hT P S).isClosed_compl.isCompact


theorem eventCutRemainder_subset :
    eventCutRemainder F T hT P S ⊆ eventCutOpen F T hT P S := by
  intro x hx hbad
  obtain ⟨i, ⟨⟨z, s⟩, ⟨_, hs⟩, hmap⟩⟩ := Set.mem_iUnion.mp hbad
  have hs0 : s = 0 := hs
  subst s
  exact hx (Set.mem_iUnion.mpr
    ⟨i, (z, 0), ⟨Set.mem_univ _, by norm_num⟩, hmap⟩)



theorem eventCutRemainder_cover {x : (F.slice (F.event T hT).tMinus).carrier}
    (hx : x ∈ eventCutOpen F T hT P S) (hnot : x ∉ eventCutRemainder F T hT P S) :
    ∃ i : S, ∃ positive : Bool, ∃ z : UnitTwoSphere, ∃ s ∈ Set.Ioo (0 : ℝ) (1 / 2),
      (P i.val).collar (cutSideReflection positive (z, s)) = x := by
  have hW : x ∈ eventCutNeighborhood F T hT P S := not_not.mp hnot
  obtain ⟨i, ⟨z, s⟩, ⟨_, hs⟩, hmap⟩ := Set.mem_iUnion.mp hW
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    exact hx (Set.mem_iUnion.mpr ⟨i, (z, 0), by simp, hmap⟩)
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · refine ⟨i, false, z, -s, ⟨by linarith, by linarith [hs.1]⟩, ?_⟩
    simpa only [cutSideReflection_apply, Bool.false_eq_true, ↓reduceIte, neg_neg] using hmap
  · refine ⟨i, true, z, s, ⟨hpos, hs.2⟩, ?_⟩
    exact hmap

end PoincareConjecture.M38
