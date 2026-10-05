import PoincareLib.Topology.Manifold.Surgery.Event.Component.ComponentBalls
import PoincareLib.Topology.Manifold.Surgery.Event.Open.OpenRegionEquivalences

/-!
# The actual balls restricted to open sides of a separating cut

Restricting the codomain of an actual ball preserves its full radius-two
coordinates. A component and its whole complement retain every unrelated
component when they form the two carriers of a reverse-cut operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (U : TopologicalSpace.Opens A.carrier)
  (hBU : B.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ U)

/-- The actual ball center in the containing open side. -/
noncomputable def openCarrierBallCenter : U :=
  ⟨B.map 0, hBU ⟨0, by simp, rfl⟩⟩

/-- Restrict the supplied ball to a containing open side, with its actual
center as the inverse inclusion's off-side fallback. -/
noncomputable def openCarrierBall : SurgeryBallEmbedding (openCarrier A U) := by
  let E := openRegionEquivalence A U (openCarrierBallCenter B U hBU)
  have hmap (z : StandardCapSpace) (hz : z ∈ Metric.ball (0 : StandardCapSpace) 2) :
      E.map (E.inverse (B.map z)) = B.map z := E.right_inverse (hBU ⟨z, hz, rfl⟩)
  refine {
    map := E.inverse ∘ B.map
    inverse := B.inverse ∘ E.map
    map_smooth := E.inverse_smooth.comp B.map_smooth (fun z hz => hBU ⟨z, hz, rfl⟩)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    open_embedding := ?_ }
  · apply B.inverse_smooth.comp (E.map_smooth.mono (Set.subset_univ _))
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, hz, (hmap z hz).symm⟩
  · intro z hz
    change B.inverse (E.map (E.inverse (B.map z))) = z
    rw [hmap z hz]
    exact B.left_inverse hz
  · rintro y ⟨z, hz, rfl⟩
    change E.inverse (B.map (B.inverse (E.map (E.inverse (B.map z))))) = E.inverse (B.map z)
    rw [hmap z hz, B.left_inverse hz]
  · apply Topology.IsOpenEmbedding.of_comp _ U.isOpen.isOpenEmbedding_subtypeVal
    have hfun : E.map ∘
        (fun z : Metric.ball (0 : StandardCapSpace) 2 => (E.inverse ∘ B.map) z.val) =
          (fun z : Metric.ball (0 : StandardCapSpace) 2 => B.map z.val) := by
      funext z
      exact hmap z.val z.property
    change Topology.IsOpenEmbedding (E.map ∘
      (fun z : Metric.ball (0 : StandardCapSpace) 2 => (E.inverse ∘ B.map) z.val))
    rw [hfun]
    exact B.open_embedding

/-- Inclusion preserves the actual ball map throughout its full radius-two domain. -/
theorem openCarrierBall_map_val {z : StandardCapSpace}
    (hz : z ∈ Metric.ball (0 : StandardCapSpace) 2) :
    ((openCarrierBall B U hBU).map z).val = B.map z :=
  (openRegionEquivalence A U (openCarrierBallCenter B U hBU)).right_inverse (hBU ⟨z, hz, rfl⟩)

/-- The restricted inverse is the original actual inverse after literal inclusion. -/
theorem openCarrierBall_inverse (z : (openCarrier A U).carrier) :
    (openCarrierBall B U hBU).inverse z = B.inverse z.val := rfl

/-- The restricted closed unit ball has exactly its original ambient image. -/
theorem openCarrierBall_closedBall_image :
    Subtype.val '' (openCarrierBall B U hBU).closedBall = B.closedBall := by
  change Subtype.val '' ((openCarrierBall B U hBU).map '' Metric.closedBall (0 : StandardCapSpace) 1) =
    B.map '' Metric.closedBall (0 : StandardCapSpace) 1
  rw [← Set.image_comp]
  apply Set.image_congr
  intro z hz
  exact openCarrierBall_map_val B U hBU
    (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz)

/-- Membership in the restricted closed ball is exactly ambient membership. -/
theorem openCarrierBall_mem_closedBall (y : (openCarrier A U).carrier) :
    y ∈ (openCarrierBall B U hBU).closedBall ↔ y.val ∈ B.closedBall := by
  rw [← openCarrierBall_closedBall_image B U hBU]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, he⟩
    exact (Subtype.ext he : z = y) ▸ hz

/-- The punctured side includes onto its exact ambient punctured region. -/
theorem openCarrierBall_puncture_image :
    Subtype.val '' (openCarrierBall B U hBU).closedBallᶜ =
      (U : Set A.carrier) ∩ B.closedBallᶜ := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨z.property, fun h => hz ((openCarrierBall_mem_closedBall B U hBU z).mpr h)⟩
  · intro y hy
    exact ⟨⟨y, hy.1⟩, fun h => hy.2 ((openCarrierBall_mem_closedBall B U hBU _).mp h), rfl⟩

/-- Inclusion and its actual fallback inverse identify the whole punctured side. -/
noncomputable def openCarrierBallPuncture :
    SurgeryRegionEquivalence (openCarrier A U) A (openCarrierBall B U hBU).closedBallᶜ
      ((U : Set A.carrier) ∩ B.closedBallᶜ) := by
  let E := openRegionEquivalence A U (openCarrierBallCenter B U hBU)
  refine {
    map := E.map
    inverse := E.inverse
    map_image := openCarrierBall_puncture_image B U hBU
    inverse_image := ?_
    left_inverse := E.left_inverse.mono (Set.subset_univ _)
    right_inverse := E.right_inverse.mono Set.inter_subset_left
    map_smooth := E.map_smooth.mono (Set.subset_univ _)
    inverse_smooth := E.inverse_smooth.mono Set.inter_subset_left }
  rw [← openCarrierBall_puncture_image B U hBU]
  exact E.left_inverse.image_image' (Set.subset_univ _)

/-- The puncture identification is literal subtype inclusion at every point. -/
theorem openCarrierBallPuncture_map (y : (openCarrier A U).carrier) :
    (openCarrierBallPuncture B U hBU).map y = y.val := rfl

/-- The complement of a clopen side, with its inherited open topology. -/
def cutSideComplement (A : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens A.carrier) (hU : IsClosed (U : Set A.carrier)) :
    TopologicalSpace.Opens A.carrier := ⟨(U : Set A.carrier)ᶜ, hU.isOpen_compl⟩

/-- A nonempty clopen region and its nonempty whole complement partition
the actual ambient carrier smoothly, retaining every other component. -/
noncomputable def cutSidesDisjointUnion (A : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens A.carrier) (hU : IsClosed (U : Set A.carrier))
    (x : U) (y : cutSideComplement A U hU) :
    SmoothDisjointUnionData ![openCarrier A U, openCarrier A (cutSideComplement A U hU)] A := by
  refine {
    region := ![(U : Set A.carrier), (U : Set A.carrier)ᶜ]
    region_open := ?_
    region_closed := ?_
    identify := fun j => Fin.cases (openRegionEquivalence A U x)
      (fun k => Fin.cases (openRegionEquivalence A (cutSideComplement A U hU) y)
        (fun l => Fin.elim0 l) k) j
    pairwise_disjoint := ?_
    cover := ?_ }
  · intro j
    fin_cases j
    · exact U.isOpen
    · exact hU.isOpen_compl
  · intro j
    fin_cases j
    · exact hU
    · exact U.isOpen.isClosed_compl
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact (hjk rfl).elim
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact (hjk rfl).elim
  · apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ U
    · exact Set.mem_iUnion.mpr ⟨0, hz⟩
    · exact Set.mem_iUnion.mpr ⟨1, hz⟩

/-- Distinct actual center components put the full positive ball chart
in the complement of the negative center component. -/
theorem surgeryBall_image_subset_other_complement {A : GeneralizedSliceCarrier.{u}}
    (B₀ B₁ : SurgeryBallEmbedding A)
    (hsep : ConnectedComponents.mk (B₀.map 0) ≠ ConnectedComponents.mk (B₁.map 0)) :
    B₁.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ (connectedComponent (B₀.map 0))ᶜ := by
  intro y hy hy₀
  have hy₁ := surgeryBall_image_subset_center_component B₁ hy
  apply hsep
  exact ConnectedComponents.coe_eq_coe.mpr
    ((connectedComponent_eq hy₀).trans (connectedComponent_eq hy₁).symm)

end PoincareMT.M38
