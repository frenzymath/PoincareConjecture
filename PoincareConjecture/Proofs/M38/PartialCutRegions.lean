import PoincareConjecture.Proofs.M38.PartialCutBalls
import PoincareConjecture.Proofs.M38.PartialCutSmooth
import PoincareConjecture.Proofs.M38.Components

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))

noncomputable local instance partialRegionChartedSpace :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P S) :=
  partialCappedChartedSpace F T hT P S

theorem partialCapPatch_disjoint (a b : S × Bool) (hab : a ≠ b) :
    Disjoint (Set.range (partialCappingInclude F T hT P S (.inr a)))
      (Set.range (partialCappingInclude F T hT P S (.inr b))) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨x, rfl⟩ ⟨y, hxy⟩
  have hrel := (partialCappingOverlap F T hT P S).include_eq_iff (.inr a) (.inr b) x y
    |>.mp hxy.symm
  have hne : (Sum.inr a : PartialCappingIndex F T hT P S) ≠ .inr b :=
    fun h => hab (Sum.inr.inj h)
  have h := (cappingTransition_graph (partialCappingMap F T hT P S) hne x y).mp hrel
  exact Set.disjoint_left.mp (cutAttachmentChart_targets_disjoint F T hT P S a b hab)
    ((cutAttachmentChart F T hT P S a).map_source h.1)
    (h.2.2.symm ▸ (cutAttachmentChart F T hT P S b).map_source h.2.1)

theorem partialCapBall_subset_patch (a : S × Bool) :
    (partialCapBall F T hT P S a).closedBall ⊆
      Set.range (partialCappingInclude F T hT P S (.inr a)) := by
  rw [partialCapBall_closedBall]
  exact Set.image_subset_range _ _

theorem partialCapBall_disjoint (a b : S × Bool) (hab : a ≠ b) :
    Disjoint (partialCapBall F T hT P S a).closedBall
      (partialCapBall F T hT P S b).closedBall :=
  (partialCapPatch_disjoint F T hT P S a b hab).mono
    (partialCapBall_subset_patch F T hT P S a) (partialCapBall_subset_patch F T hT P S b)

theorem partialCapBall_disjoint_old (a : S × Bool) :
    Disjoint (partialCapBall F T hT P S a).closedBall
      (Set.range (partialOldInclusion F T hT P S)) := by
  rw [partialCapBall_closedBall]
  apply Set.disjoint_left.mpr
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy⟩
  let z : partialCappingDomain F T hT P S (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  have hz := partialOldInclusion_patch F T hT P S y z
  rw [partialCappingMap_old_center] at hz
  have heq : partialCappingInclude F T hT P S (.inr a) x =
      partialCappingInclude F T hT P S (.inl y) z := hy.symm.trans hz
  have hrel := (partialCappingOverlap F T hT P S).include_eq_iff (.inr a) (.inl y) x z
    |>.mp heq
  have h := (cappingTransition_graph (partialCappingMap F T hT P S) (by simp) x z).mp hrel
  have hnorm : 1 < ‖x.val‖ := by
    have hsrc := h.1
    change x ∈ (cutAttachmentChart F T hT P S a).source at hsrc
    rwa [cutAttachmentChart_source] at hsrc
  exact (not_lt_of_ge hx) hnorm

theorem partialOldInclusion_range :
    Set.range (partialOldInclusion F T hT P S) =
      (⋃ a : S × Bool, (partialCapBall F T hT P S a).closedBall)ᶜ := by
  apply Set.Subset.antisymm
  · intro q hq hcap
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hcap
    exact Set.disjoint_left.mp (partialCapBall_disjoint_old F T hT P S a) ha hq
  · intro q
    induction q using Quotient.inductionOn with
    | h a =>
        rcases a with ⟨j, x⟩
        cases j with
        | inl y =>
            intro _
            exact ⟨partialCappingMap F T hT P S (.inl y) x,
              partialOldInclusion_patch F T hT P S y x⟩
        | inr a =>
            intro hx
            have hnorm : 1 < ‖x.val‖ := by
              by_contra h
              apply hx
              apply Set.mem_iUnion.mpr
              refine ⟨a, ?_⟩
              rw [partialCapBall_closedBall]
              exact ⟨x, le_of_not_gt h, rfl⟩
            exact ⟨cutAttachmentChart F T hT P S a x,
              partialOldInclusion_cap F T hT P S a x hnorm⟩

noncomputable def partialOldRegionEquivalence :
    SurgeryRegionEquivalence
      (openCarrier (F.slice (F.event T hT).tMinus) (eventCutOpen F T hT P S))
      (partialCappedCarrier F T hT P S) Set.univ
      ((⋃ a : S × Bool, (partialCapBall F T hT P S a).closedBall)ᶜ) where
  map := partialOldInclusion F T hT P S
  inverse := partialOldInverse F T hT P S
  map_image := by rw [Set.image_univ, partialOldInclusion_range]
  inverse_image := by
    rw [← partialOldInclusion_range]
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨partialOldInclusion F T hT P S y, Set.mem_range_self y,
      partialOldInverse_apply F T hT P S y⟩
  left_inverse := fun y _ => partialOldInverse_apply F T hT P S y
  right_inverse := by
    rw [← partialOldInclusion_range]
    exact fun _ hq => partialOldInverse_right F T hT P S hq
  map_smooth := (partialOldInclusion_smooth F T hT P S).contMDiffOn
  inverse_smooth := by
    rw [← partialOldInclusion_range]
    exact partialOldInverse_smooth F T hT P S

end PoincareConjecture.M38
