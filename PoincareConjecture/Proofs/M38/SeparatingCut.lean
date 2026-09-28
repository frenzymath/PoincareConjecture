import PoincareConjecture.Proofs.M38.SingleCutRegions
import PoincareConjecture.Proofs.M38.CutBallSides
import PoincareConjecture.Proofs.M38.BallCoordinatePatch
import PoincareConjecture.Proofs.M38.UnionRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count)

noncomputable def singleCutSideIdentify
    (B : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))
    (U : TopologicalSpace.Opens (partialCappedCarrier F T hT P (insert i S)).carrier)
    (hBU : B.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ U)
    (hW : (U : Set (partialCappedCarrier F T hT P (insert i S)).carrier) ∩ B.closedBallᶜ ⊆
      sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S)) :
    SurgeryRegionEquivalence (openCarrier (partialCappedCarrier F T hT P (insert i S)) U)
      (partialCappedCarrier F T hT P S) (openCarrierBall B U hBU).closedBallᶜ
      ((singleCutRegionEquivalence F T hT P S i).map ''
        ((U : Set (partialCappedCarrier F T hT P (insert i S)).carrier) ∩ B.closedBallᶜ)) :=
  composeRegions (openCarrierBallPuncture B U hBU)
    (restrictRegions (singleCutRegionEquivalence F T hT P S i) _ hW)

theorem singleCutSideIdentify_map
    (B : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))
    (U : TopologicalSpace.Opens (partialCappedCarrier F T hT P (insert i S)).carrier)
    (hBU : B.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ U)
    (hW : (U : Set (partialCappedCarrier F T hT P (insert i S)).carrier) ∩ B.closedBallᶜ ⊆
      sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S))
    (y : (openCarrier (partialCappedCarrier F T hT P (insert i S)) U).carrier) :
    (singleCutSideIdentify F T hT P S i B U hBU hW).map y =
      (singleCutRegionEquivalence F T hT P S i).map y.val := rfl

theorem singleCutSideRegion_open
    (B : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))
    (U : TopologicalSpace.Opens (partialCappedCarrier F T hT P (insert i S)).carrier)
    (hW : (U : Set (partialCappedCarrier F T hT P (insert i S)).carrier) ∩ B.closedBallᶜ ⊆
      sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S)) :
    IsOpen ((singleCutRegionEquivalence F T hT P S i).map ''
      ((U : Set (partialCappedCarrier F T hT P (insert i S)).carrier) ∩ B.closedBallᶜ)) := by
  let e := regionPartialDiffeomorph (singleCutRegionEquivalence F T hT P S i)
    (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S)).isOpen
    (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S)).isOpen
  exact e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (U.isOpen.inter (surgeryBall_closedImage_compact B 1 (by norm_num)).isClosed.isOpen_compl) hW

variable (hi : i ∉ S)

theorem singleCutRegionEquivalence_collar (positive : Bool) (z : UnitTwoSphere)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    uncutCollar F T hT P S i hi (cutSideReflection positive (z, s)) =
      (singleCutRegionEquivalence F T hT P S i).map
        ((singleCutBall F T hT P S i positive).map (capAttachVector (z, s))) := by
  have hz : (z, s) ∈ (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (0 : ℝ) 1 :=
    ⟨Set.mem_univ _, hs⟩
  have hnorm := capAttachVector_mem hz
  let x : capDoubleBall := ⟨capAttachVector (z, s), by
    simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk, Metric.mem_ball, dist_zero_right]
      using hnorm.2⟩
  have hx : 1 < ‖x.val‖ := hnorm.1
  change uncutCollar F T hT P S i hi (cutSideReflection positive (z, s)) =
    (singleCutRegionEquivalence F T hT P S i).map
      ((singleCutBall F T hT P S i positive).map x.val)
  rw [singleCutRegionEquivalence_annulus F T hT P S i positive x hx, uncutCollar_apply]
  apply congrArg (partialOldInclusion F T hT P S)
  apply Subtype.ext
  rw [uncutCollarOldChart_apply F T hT P S i hi _
    ((cutSideReflection_mem_full positive (z, s)).mpr (positive_collar_subset hz))]
  change (P i).collar (cutSideReflection positive (z, s)) =
    (cutAttachmentChart F T hT P (insert i S) (⟨i, Set.mem_insert i S⟩, positive) x).val
  rw [cutAttachmentChart_apply F T hT P (insert i S) (⟨i, Set.mem_insert i S⟩, positive) hx]
  change (P i).collar (cutSideReflection positive (z, s)) =
    (P i).collar (cutSideReflection positive (capAttachCoordinates (capAttachVector (z, s))))
  rw [capAttachCoordinates_vector hz]

include hi in

theorem singleCut_separating_step
    (hsep : ConnectedComponents.mk ((singleCutBall F T hT P S i false).map 0) ≠
      ConnectedComponents.mk ((singleCutBall F T hT P S i true).map 0)) :
    SmoothConnectedSumStep (partialCappedCarrier F T hT P (insert i S))
      (partialCappedCarrier F T hT P S) := by
  classical
  let A := partialCappedCarrier F T hT P (insert i S)
  let B₀ := singleCutBall F T hT P S i false
  let B₁ := singleCutBall F T hT P S i true
  let U := componentOpen A (B₀.map 0)
  have hU : IsClosed (U : Set A.carrier) := isClosed_connectedComponent
  let V := cutSideComplement A U hU
  have hB₀ : B₀.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ U :=
    surgeryBall_image_subset_center_component B₀
  have hB₁ : B₁.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ V :=
    surgeryBall_image_subset_other_complement B₀ B₁ hsep
  have hb₀ : B₀.closedBall ⊆ U := (surgeryBall_closedBall_subset_image B₀).trans hB₀
  have hb₁ : B₁.closedBall ⊆ V := (surgeryBall_closedBall_subset_image B₁).trans hB₁
  let W₀ : Set A.carrier := (U : Set A.carrier) ∩ B₀.closedBallᶜ
  let W₁ : Set A.carrier := (V : Set A.carrier) ∩ B₁.closedBallᶜ
  let W := sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S)
  let K := sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S)
  let E := singleCutRegionEquivalence F T hT P S i
  have hw₀ : W₀ ⊆ W := by
    intro y hy
    rw [singleCut_sharedOpen F T hT P S i hi]
    intro hbad
    rcases hbad with hb | hb
    · exact hy.2 hb
    · exact (hb₁ hb) hy.1
  have hw₁ : W₁ ⊆ W := by
    intro y hy
    rw [singleCut_sharedOpen F T hT P S i hi]
    intro hbad
    rcases hbad with hb | hb
    · exact hy.1 (hb₀ hb)
    · exact hy.2 hb
  have hw : W₀ ∪ W₁ = (W : Set A.carrier) := by
    apply Set.Subset.antisymm (Set.union_subset hw₀ hw₁)
    intro y hy
    have hnot : y ∉ B₀.closedBall ∪ B₁.closedBall := by
      change y ∈ (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) :
        Set (partialCappedCarrier F T hT P (insert i S)).carrier) at hy
      rw [singleCut_sharedOpen F T hT P S i hi] at hy
      exact hy
    by_cases hyU : y ∈ U
    · exact Or.inl ⟨hyU, fun h => hnot (Or.inl h)⟩
    · exact Or.inr ⟨hyU, fun h => hnot (Or.inr h)⟩
  let e₀ := singleCutSideIdentify F T hT P S i B₀ U hB₀ hw₀
  let e₁ := singleCutSideIdentify F T hT P S i B₁ V hB₁ hw₁
  have hregions : E.map '' W₀ ∪ E.map '' W₁ = (K : Set (partialCappedCarrier F T hT P S).carrier) := by
    rw [← Set.image_union, hw]
    exact E.map_image
  let c := uncutCollar F T hT P S i hi
  have hc : c.source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := uncutCollar_source F T hT P S i hi
  refine ⟨openCarrier A U, openCarrier A V,
    ⟨cutSidesDisjointUnion A U hU (openCarrierBallCenter B₀ U hB₀)
      (openCarrierBallCenter B₁ V hB₁)⟩, ⟨{
    first_ball := openCarrierBall B₀ U hB₀
    second_ball := openCarrierBall B₁ V hB₁
    first_region := E.map '' W₀
    second_region := E.map '' W₁
    first_open := singleCutSideRegion_open F T hT P S i B₀ U hw₀
    second_open := singleCutSideRegion_open F T hT P S i B₁ V hw₁
    first_identify := e₀
    second_identify := e₁
    regions_disjoint := ?_
    sphere_gluing := Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞
    collar := c
    collar_inverse := c.symm
    collar_smooth := hc ▸ c.contMDiffOn_toFun
    collar_inverse_smooth := ?_
    collar_left_inverse := fun _ hz => c.left_inv (hc.symm ▸ hz)
    collar_right_inverse := ?_
    collar_open := uncutCollar_image_open F T hT P S i hi
    negative_gluing := ?_
    positive_gluing := ?_
    central_disjoint := ?_
    cover := ?_ }⟩⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have hba : b = a := by
      calc
        b = E.inverse (E.map b) := (E.left_inverse (hw₁ hb)).symm
        _ = E.inverse (E.map a) := congrArg E.inverse heq
        _ = a := E.left_inverse (hw₀ ha)
    exact hb.1 (hba.symm ▸ ha.1)
  · rw [uncutCollar_image]
    exact c.contMDiffOn_invFun
  · intro y hy
    exact c.right_inv ((uncutCollar_image F T hT P S i hi).subset hy)
  · intro z s hs
    have hs' : -s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hz : (z, -s) ∈ (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (0 : ℝ) 1 :=
      ⟨Set.mem_univ _, hs'⟩
    have hball : (1 - s) • z.val ∈ Metric.ball (0 : StandardCapSpace) 2 := by
      simpa only [capAttachVector, sub_eq_add_neg, Metric.mem_ball, dist_zero_right]
        using (capAttachVector_mem hz).2
    change c (z, s) = E.map (((openCarrierBall B₀ U hB₀).map ((1 - s) • z.val)).val)
    rw [openCarrierBall_map_val B₀ U hB₀ hball]
    simpa only [cutSideReflection_apply, Bool.false_eq_true, ↓reduceIte, neg_neg,
      capAttachVector, sub_eq_add_neg]
      using singleCutRegionEquivalence_collar F T hT P S i hi false z (-s) hs'
  · intro z s hs
    have hz : (z, s) ∈ (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (0 : ℝ) 1 :=
      ⟨Set.mem_univ _, hs⟩
    have hball : (1 + s) • z.val ∈ Metric.ball (0 : StandardCapSpace) 2 := by
      simpa only [capAttachVector, Metric.mem_ball, dist_zero_right] using (capAttachVector_mem hz).2
    change c (z, s) = E.map (((openCarrierBall B₁ V hB₁).map ((1 + s) • z.val)).val)
    rw [openCarrierBall_map_val B₁ V hB₁ hball]
    simpa only [cutSideReflection_apply, ↓reduceIte, capAttachVector]
      using singleCutRegionEquivalence_collar F T hT P S i hi true z s hs
  · rw [hregions]
    change Disjoint (uncutCollar F T hT P S i hi '' (Set.univ ×ˢ ({0} : Set ℝ)))
      (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S) :
        Set (partialCappedCarrier F T hT P S).carrier)
    rw [singleCut_targetOpen F T hT P S i hi]
    exact disjoint_compl_right
  · rw [hregions]
    change (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S) :
        Set (partialCappedCarrier F T hT P S).carrier) ∪
      (uncutCollar F T hT P S i hi '' (Set.univ ×ˢ ({0} : Set ℝ))) = Set.univ
    rw [singleCut_targetOpen F T hT P S i hi]
    exact Set.compl_union_self _

end PoincareConjecture.M38
