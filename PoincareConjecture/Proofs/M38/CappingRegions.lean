import PoincareConjecture.Proofs.M38.CappingBalls
import PoincareConjecture.Proofs.M38.CappingSmooth
import PoincareConjecture.Proofs.M38.Components









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable local instance cappedRegionChartedSpace :
    ChartedSpace StandardCapSpace (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedChartedSpace F T hT P


theorem cappedCapPatch_disjoint (i j : Fin (F.event T hT).cap_count) (hij : i ≠ j) :
    Disjoint (Set.range (eventCappingInclude F T hT P (.inr i)))
      (Set.range (eventCappingInclude F T hT P (.inr j))) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨x, rfl⟩ ⟨y, hxy⟩
  have hrel := (eventCappingOverlap F T hT P).include_eq_iff (.inr i) (.inr j) x y |>.mp hxy.symm
  have hne : (Sum.inr i : EventCappingIndex F T hT) ≠ .inr j :=
    fun h => hij (Sum.inr.inj h)
  have h := (cappingTransition_graph (eventCappingMap F T hT P) hne x y).mp hrel
  exact Set.disjoint_left.mp ((P i).attachmentChart_targets_disjoint (P j) hij)
    ((P i).attachmentChart.map_source h.1)
    (h.2.2.symm ▸ (P j).attachmentChart.map_source h.2.1)


theorem cappedCapBall_subset_patch (i : Fin (F.event T hT).cap_count) :
    (cappedCapBall F T hT P i).closedBall ⊆
      Set.range (eventCappingInclude F T hT P (.inr i)) := by
  rw [cappedCapBall_closedBall]
  exact Set.image_subset_range _ _


theorem cappedCapBall_disjoint (i j : Fin (F.event T hT).cap_count) (hij : i ≠ j) :
    Disjoint (cappedCapBall F T hT P i).closedBall (cappedCapBall F T hT P j).closedBall :=
  (cappedCapPatch_disjoint F T hT P i j hij).mono
    (cappedCapBall_subset_patch F T hT P i) (cappedCapBall_subset_patch F T hT P j)


theorem cappedCapBall_disjoint_old (i : Fin (F.event T hT).cap_count) :
    Disjoint (cappedCapBall F T hT P i).closedBall
      (Set.range (cappedOldInclusion F T hT P)) := by
  rw [cappedCapBall_closedBall]
  apply Set.disjoint_left.mpr
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy⟩
  let z : eventCappingDomain F T hT (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  have hz := cappedOldInclusion_patch F T hT P y z
  rw [eventCappingMap_old_center] at hz
  have heq : eventCappingInclude F T hT P (.inr i) x =
      eventCappingInclude F T hT P (.inl y) z := hy.symm.trans hz
  have hrel := (eventCappingOverlap F T hT P).include_eq_iff (.inr i) (.inl y) x z |>.mp heq
  have h := (cappingTransition_graph (eventCappingMap F T hT P) (by simp) x z).mp hrel
  have hnorm : 1 < ‖x.val‖ := by
    have hsrc := h.1
    change x ∈ (P i).attachmentChart.source at hsrc
    rwa [(P i).attachmentChart_source] at hsrc
  exact (not_lt_of_ge hx) hnorm


theorem cappedOldInclusion_range :
    Set.range (cappedOldInclusion F T hT P) =
      (⋃ i, (cappedCapBall F T hT P i).closedBall)ᶜ := by
  apply Set.Subset.antisymm
  · intro q hq hcap
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcap
    exact Set.disjoint_left.mp (cappedCapBall_disjoint_old F T hT P i) hi hq
  · intro q
    induction q using Quotient.inductionOn with
    | h a =>
        rcases a with ⟨j, x⟩
        cases j with
        | inl y =>
            intro _
            exact ⟨eventCappingMap F T hT P (.inl y) x,
              cappedOldInclusion_patch F T hT P y x⟩
        | inr i =>
            intro hx
            have hnorm : 1 < ‖x.val‖ := by
              by_contra h
              apply hx
              apply Set.mem_iUnion.mpr
              refine ⟨i, ?_⟩
              rw [cappedCapBall_closedBall]
              exact ⟨x, le_of_not_gt h, rfl⟩
            exact ⟨(P i).attachmentChart x, cappedOldInclusion_cap F T hT P i x hnorm⟩



noncomputable def cappedOldRegionEquivalence :
    SurgeryRegionEquivalence
      (openCarrier (F.slice (F.event T hT).tMinus) (eventDiscardedOpen F T hT))
      (cappedDiscardedCarrier F T hT P) Set.univ
      ((⋃ i, (cappedCapBall F T hT P i).closedBall)ᶜ) where
  map := cappedOldInclusion F T hT P
  inverse := cappedOldInverse F T hT P
  map_image := by rw [Set.image_univ, cappedOldInclusion_range]
  inverse_image := by
    rw [← cappedOldInclusion_range]
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨cappedOldInclusion F T hT P y, Set.mem_range_self y,
      cappedOldInverse_apply F T hT P y⟩
  left_inverse := fun y _ => cappedOldInverse_apply F T hT P y
  right_inverse := by
    rw [← cappedOldInclusion_range]
    exact fun _ hq => cappedOldInverse_right F T hT P hq
  map_smooth := (cappedOldInclusion_smooth F T hT P).contMDiffOn
  inverse_smooth := by
    rw [← cappedOldInclusion_range]
    exact cappedOldInverse_smooth F T hT P

end PoincareConjecture.M38
