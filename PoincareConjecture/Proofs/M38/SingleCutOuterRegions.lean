import PoincareConjecture.Proofs.M38.SingleCutHandleCoordinates
import PoincareConjecture.Proofs.M38.ReciprocalEnclosingCollar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)

local notation "A" => partialCappedCarrier F T hT P (insert i S)
local notation "X" => partialCappedCarrier F T hT P S
local notation "B₀" => singleCutBall F T hT P S i false
local notation "B₁" => singleCutBall F T hT P S i true
local notation "E" => singleCutRegionEquivalence F T hT P S i
local notation "c" => uncutCollar F T hT P S i hi

variable (C : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))
  {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (hB₀ : (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)
  (hB₁ : (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)

local notation "D" => reciprocalEnclosingBall C ha ha8
local notation "W" => enclosingInnerTwoHoleRegion C B₀ B₁
local notation "J" => C.map '' Metric.sphere 0 (3 / 2)

include hB₀ hB₁ in

theorem singleCut_balls_subset_enclosing_unit :
    (B₀).closedBall ∪ (B₁).closedBall ⊆ C.map '' Metric.ball 0 1 := by
  apply Set.union_subset
  · exact (Set.image_mono (Metric.closedBall_subset_closedBall
      (by norm_num : (1 : ℝ) ≤ 5 / 4))).trans hB₀
  · exact (Set.image_mono (Metric.closedBall_subset_closedBall
      (by norm_num : (1 : ℝ) ≤ 5 / 4))).trans hB₁

include hi hB₀ hB₁ in

theorem singleCut_enclosingExterior_subset_shared :
    (D).closedBallᶜ ⊆ sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) := by
  rw [singleCut_sharedOpen F T hT P S i hi]
  intro x hx hballs
  exact hx (reciprocalEnclosingBall_contains_unit C ha ha8
    (singleCut_balls_subset_enclosing_unit F T hT P S i C hB₀ hB₁ hballs))

include hi ha ha8 hB₀ hB₁ in

theorem singleCut_enclosingSphere_subset_shared :
    J ⊆ sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) := by
  have hdis := reciprocalEnclosingCollar_central_disjoint C ha ha8
  rw [reciprocalEnclosingCollar_central] at hdis
  rw [singleCut_sharedOpen F T hT P S i hi]
  intro x hx hballs
  have hunit := singleCut_balls_subset_enclosing_unit F T hT P S i C hB₀ hB₁ hballs
  have hinner : x ∈ C.map '' Metric.ball 0 (3 / 2) :=
    (Set.image_mono (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 3 / 2))) hunit
  exact Set.disjoint_left.mp hdis hx (Or.inl hinner)

include hi hB₀ hB₁ in

theorem singleCut_enclosing_partition :
    (D).closedBallᶜ ∪ W ∪ J =
      (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) : Set (A).carrier) := by
  apply Set.Subset.antisymm
  · exact Set.union_subset
      (Set.union_subset
        (singleCut_enclosingExterior_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁)
        (singleCut_innerTwoHole_subset_shared F T hT P S i hi C))
      (singleCut_enclosingSphere_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁)
  · intro x hx
    have hholes : x ∉ (B₀).closedBall ∪ (B₁).closedBall :=
      (singleCut_sharedOpen F T hT P S i hi).subset hx
    by_cases hclosed : x ∈ (D).closedBall
    · rw [reciprocalEnclosingBall_closedBall] at hclosed
      obtain ⟨v, hv, rfl⟩ := hclosed
      have hvnorm : ‖v‖ ≤ 3 / 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hv
      rcases lt_or_eq_of_le hvnorm with hlt | heq
      · exact Or.inl (Or.inr ⟨⟨v, by
          simpa only [Metric.mem_ball, dist_zero_right] using hlt, rfl⟩, hholes⟩)
      · exact Or.inr ⟨v, by
          simpa only [Metric.mem_sphere, dist_zero_right] using heq, rfl⟩
    · exact Or.inl (Or.inl hclosed)


def singleCutExteriorRegion : Set (X).carrier := (E).map '' (D).closedBallᶜ


def singleCutOuterSphere : Set (X).carrier := (E).map '' J

include hi hB₀ hB₁ in

noncomputable def singleCutExteriorIdentify :
    SurgeryRegionEquivalence A X (D).closedBallᶜ
      (singleCutExteriorRegion F T hT P S i C ha ha8) :=
  restrictRegions E (D).closedBallᶜ
    (singleCut_enclosingExterior_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁)


theorem singleCutExteriorIdentify_map (x : (A).carrier) :
    (singleCutExteriorIdentify F T hT P S i hi C ha ha8 hB₀ hB₁).map x = (E).map x := rfl


theorem singleCutExteriorIdentify_inverse (x : (X).carrier) :
    (singleCutExteriorIdentify F T hT P S i hi C ha ha8 hB₀ hB₁).inverse x =
      (E).inverse x := rfl

include hi hB₀ hB₁ in

theorem singleCutExteriorRegion_open :
    IsOpen (singleCutExteriorRegion F T hT P S i C ha ha8) := by
  let e := regionPartialDiffeomorph E
    (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S)).isOpen
    (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S)).isOpen
  exact e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (surgeryBall_closedImage_compact D 1 (by norm_num)).isClosed.isOpen_compl
    (singleCut_enclosingExterior_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁)

include hi hB₀ hB₁ in

theorem singleCutExteriorRegion_disjoint_handle :
    Disjoint (singleCutExteriorRegion F T hT P S i C ha ha8)
      (singleCutHandleOpen F T hT P S i C ∪ comparisonCentralSphere c) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ (hinner | hcentral)
  · obtain ⟨z, hz, hzx⟩ := hinner
    have heq : z = x := (E).left_inverse.injOn
      (singleCut_innerTwoHole_subset_shared F T hT P S i hi C hz)
      (singleCut_enclosingExterior_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁ hx) hzx
    apply hx
    rw [reciprocalEnclosingBall_closedBall]
    exact heq ▸ (Set.image_mono Metric.ball_subset_closedBall hz.1)
  · have htarget := (E).map_image.subset ⟨x,
      singleCut_enclosingExterior_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁ hx, rfl⟩
    exact ((singleCut_targetOpen F T hT P S i hi).subset htarget) hcentral

include hi hB₀ hB₁ in

theorem singleCutOuterSphere_disjoint_regions :
    Disjoint (singleCutOuterSphere F T hT P S i C)
      (singleCutExteriorRegion F T hT P S i C ha ha8 ∪
        (singleCutHandleOpen F T hT P S i C ∪ comparisonCentralSphere c)) := by
  have hdis := reciprocalEnclosingCollar_central_disjoint C ha ha8
  rw [reciprocalEnclosingCollar_central] at hdis
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ (houter | hinner | hcentral)
  · obtain ⟨z, hz, hzx⟩ := houter
    have heq : z = x := (E).left_inverse.injOn
      (singleCut_enclosingExterior_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁ hz)
      (singleCut_enclosingSphere_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁ hx) hzx
    exact Set.disjoint_left.mp hdis hx (Or.inr (heq ▸ hz))
  · obtain ⟨z, hz, hzx⟩ := hinner
    have heq : z = x := (E).left_inverse.injOn
      (singleCut_innerTwoHole_subset_shared F T hT P S i hi C hz)
      (singleCut_enclosingSphere_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁ hx) hzx
    exact Set.disjoint_left.mp hdis hx (Or.inl (heq ▸ hz.1))
  · have htarget := (E).map_image.subset ⟨x,
      singleCut_enclosingSphere_subset_shared F T hT P S i hi C ha ha8 hB₀ hB₁ hx, rfl⟩
    exact ((singleCut_targetOpen F T hT P S i hi).subset htarget) hcentral

include hi hB₀ hB₁ in

theorem singleCutOuterRegions_image_partition :
    singleCutExteriorRegion F T hT P S i C ha ha8 ∪
      singleCutHandleOpen F T hT P S i C ∪ singleCutOuterSphere F T hT P S i C =
        (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S) : Set (X).carrier) := by
  change (E).map '' (D).closedBallᶜ ∪ (E).map '' W ∪ (E).map '' J = _
  rw [← Set.image_union, ← Set.image_union,
    singleCut_enclosing_partition F T hT P S i hi C ha ha8 hB₀ hB₁]
  exact (E).map_image

include hB₀ hB₁ in


theorem singleCutOuterRegions_cover :
    singleCutExteriorRegion F T hT P S i C ha ha8 ∪
      (singleCutHandleOpen F T hT P S i C ∪ comparisonCentralSphere c) ∪
        singleCutOuterSphere F T hT P S i C = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _
  by_cases hcentral : x ∈ comparisonCentralSphere c
  · exact Or.inl (Or.inr (Or.inr hcentral))
  · have htarget : x ∈ sharedCutTargetOpen F T hT P S (insert i S)
        (Set.subset_insert i S) := by
      exact (singleCut_targetOpen F T hT P S i hi).symm.subset hcentral
    have himage := (singleCutOuterRegions_image_partition F T hT P S i hi C ha ha8
      hB₀ hB₁).symm.subset htarget
    rcases himage with (houter | hinner) | hsphere
    · exact Or.inl (Or.inl houter)
    · exact Or.inl (Or.inr (Or.inl hinner))
    · exact Or.inr hsphere


theorem singleCutOuterSphere_collar :
    singleCutOuterSphere F T hT P S i C =
      (E).map '' (reciprocalEnclosingCollar C ha ha8 '' (Set.univ ×ˢ ({0} : Set ℝ))) := by
  rw [reciprocalEnclosingCollar_central]
  rfl

end PoincareConjecture.M38
