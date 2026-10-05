import PoincareLib.Topology.Manifold.Surgery.Event.Shared.SharedCutDiffeomorph
import PoincareLib.Topology.Manifold.Surgery.Event.Uncut.UncutCollar
import PoincareLib.Topology.Manifold.Surgery.Event.Open.OpenRegionEquivalences

/-!
# The exact regions for undoing one actual cut

Adding one selected event sphere introduces exactly its two signed balls.
The shared diffeomorphism omits those balls and exactly the central sphere
of the actual uncut collar in the preceding partial capped carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count)

/-- The literal signed ball added by selecting this one event sphere. -/
noncomputable def singleCutBall (positive : Bool) :
    SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)) :=
  partialCapBall F T hT P (insert i S) (⟨i, Set.mem_insert i S⟩, positive)

variable (hi : i ∉ S)

include hi in
/-- The newly introduced closed balls are precisely the two actual signed balls. -/
theorem singleCut_newBalls :
    newCutBalls F T hT P S (insert i S) =
      (singleCutBall F T hT P S i false).closedBall ∪
        (singleCutBall F T hT P S i true).closedBall := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hq
    have hai : a.val.1.val = i := (Set.mem_insert_iff.mp a.val.1.property).resolve_right a.property
    have heq : a.val = (⟨i, Set.mem_insert i S⟩, a.val.2) :=
      Prod.ext (Subtype.ext hai) rfl
    rw [heq] at ha
    cases hs : a.val.2
    · simp only [hs] at ha
      exact Or.inl ha
    · simp only [hs] at ha
      exact Or.inr ha
  · intro q hq
    rcases hq with hq | hq
    · exact Set.mem_iUnion.mpr ⟨⟨(⟨i, Set.mem_insert i S⟩, false), hi⟩, hq⟩
    · exact Set.mem_iUnion.mpr ⟨⟨(⟨i, Set.mem_insert i S⟩, true), hi⟩, hq⟩

include hi in
/-- Only the actual i central sphere is newly removed from the old domain. -/
theorem singleCut_newSpheres :
    eventCutSpheres F T hT P (insert i S \ S) =
      (P i).collar '' (Set.univ ×ˢ ({0} : Set ℝ)) := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    have hji : j.val = i := (Set.mem_insert_iff.mp j.property.1).resolve_right j.property.2
    change q ∈ (P j.val).collar '' (Set.univ ×ˢ ({0} : Set ℝ)) at hj
    rw [hji] at hj
    exact hj
  · intro q hq
    exact Set.mem_iUnion.mpr ⟨⟨i, Set.mem_insert i S, hi⟩, hq⟩

/-- The omitted target sphere is the central image of the actual uncut collar. -/
theorem singleCut_newSphereImage :
    newCutSphereImage F T hT P S (insert i S) =
      uncutCollar F T hT P S i hi '' (Set.univ ×ˢ ({0} : Set ℝ)) := by
  rw [uncutCollar_central]
  unfold newCutSphereImage
  rw [singleCut_newSpheres F T hT P S i hi]

include hi in
/-- The shared source deletes exactly the negative and positive new closed balls. -/
theorem singleCut_sharedOpen :
    (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) :
      Set (partialCappedCarrier F T hT P (insert i S)).carrier) =
        ((singleCutBall F T hT P S i false).closedBall ∪
          (singleCutBall F T hT P S i true).closedBall)ᶜ := by
  rw [sharedCutOpen_eq_compl_newBalls, singleCut_newBalls F T hT P S i hi]

/-- The shared target deletes exactly the actual uncut central sphere. -/
theorem singleCut_targetOpen :
    (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S) :
      Set (partialCappedCarrier F T hT P S).carrier) =
        (uncutCollar F T hT P S i hi '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ := by
  change (newCutSphereImage F T hT P S (insert i S))ᶜ = _
  rw [singleCut_newSphereImage F T hT P S i hi]

/-- An actual old annulus point supplies the total-map fallback for the comparison. -/
noncomputable def singleCutSharedPoint :
    sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) := by
  let y : eventCutOpen F T hT P (insert i S) :=
    ⟨(P i).collar (cutSideReflection false (capUnitDirection 0, 1 / 2)),
      cutAnnularChart_target_cutOpen F T hT P (insert i S) i false
        ⟨(capUnitDirection 0, 1 / 2), ⟨Set.mem_univ _, by norm_num⟩, rfl⟩⟩
  exact ⟨partialOldInclusion F T hT P (insert i S) y,
    partialOldInclusion_mem_shared F T hT P S (insert i S) (Set.subset_insert i S) y⟩

/-- The actual shared diffeomorphism as an ambient region equivalence. -/
noncomputable def singleCutRegionEquivalence :
    SurgeryRegionEquivalence (partialCappedCarrier F T hT P (insert i S))
      (partialCappedCarrier F T hT P S)
      (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S))
      (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S)) :=
  openDiffeomorphRegions _ _
    (sharedCutDiffeomorph F T hT P S (insert i S) (Set.subset_insert i S))
    (singleCutSharedPoint F T hT P S i)

/-- On every actual signed outer annulus, the ambient map keeps the old attachment point. -/
theorem singleCutRegionEquivalence_annulus (positive : Bool) (x : capDoubleBall)
    (hx : 1 < ‖x.val‖) :
    (singleCutRegionEquivalence F T hT P S i).map
      ((singleCutBall F T hT P S i positive).map x.val) =
        partialOldInclusion F T hT P S (successiveOldInclusion F T hT P S
          (insert i S) (Set.subset_insert i S)
          (cutAttachmentChart F T hT P (insert i S) (⟨i, Set.mem_insert i S⟩, positive) x)) := by
  have hmem : (singleCutBall F T hT P S i positive).map x.val ∈
      sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) :=
    partialCapBall_annulus_mem_shared F T hT P S (insert i S) (Set.subset_insert i S)
      (⟨i, Set.mem_insert i S⟩, positive) x hx
  have heq := openDiffeomorphRegions_apply
    (A := partialCappedCarrier F T hT P (insert i S)) (B := partialCappedCarrier F T hT P S)
    (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S))
    (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S))
    (sharedCutDiffeomorph F T hT P S (insert i S) (Set.subset_insert i S))
    (singleCutSharedPoint F T hT P S i) ((singleCutBall F T hT P S i positive).map x.val) hmem
  exact heq.trans (sharedCutDiffeomorph_annulus F T hT P S (insert i S) (Set.subset_insert i S)
    (⟨i, Set.mem_insert i S⟩, positive) x hx)

end PoincareMT.M38
