import PoincareLib.Topology.Manifold.Surgery.Event.Ball.BallTransport
import PoincareLib.Topology.Manifold.Surgery.Event.Full.FullCutLocalModels
import PoincareLib.Topology.Manifold.Surgery.Event.Ball.BallPuncture

/-!
# Transporting supplied balls through exact open region coordinates

An actual ball whose full chart lies in the source of a region
equivalence keeps all its coordinates after transport. Removing that
ball on both sides restricts the same equivalence to the exact complements.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A D : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set D.carrier}
  (B : SurgeryBallEmbedding A) (E : SurgeryRegionEquivalence A D U V)
  (hU : IsOpen U) (hV : IsOpen V) (hBU : B.map '' Metric.ball 0 2 ⊆ U)

/-- Transport the whole radius-two ball chart through the actual open region coordinates. -/
noncomputable def transportSurgeryBallRegion : SurgeryBallEmbedding D where
  map := E.map ∘ B.map
  inverse := B.inverse ∘ E.inverse
  map_smooth := E.map_smooth.comp B.map_smooth (fun x hx => hBU ⟨x, hx, rfl⟩)
  inverse_smooth := by
    apply B.inverse_smooth.comp (E.inverse_smooth.mono ?_) ?_
    · rintro y ⟨x, hx, rfl⟩
      exact E.map_image.subset (Set.mem_image_of_mem _ (hBU ⟨x, hx, rfl⟩))
    · rintro y ⟨x, hx, rfl⟩
      change E.inverse (E.map (B.map x)) ∈ B.map '' Metric.ball 0 2
      rw [E.left_inverse (hBU ⟨x, hx, rfl⟩)]
      exact ⟨x, hx, rfl⟩
  left_inverse := by
    intro x hx
    change B.inverse (E.inverse (E.map (B.map x))) = x
    rw [E.left_inverse (hBU ⟨x, hx, rfl⟩), B.left_inverse hx]
  right_inverse := by
    rintro y ⟨x, hx, rfl⟩
    change E.map (B.map (B.inverse (E.inverse (E.map (B.map x))))) = E.map (B.map x)
    rw [E.left_inverse (hBU ⟨x, hx, rfl⟩), B.left_inverse hx]
  open_embedding := by
    let f : Metric.ball (0 : StandardCapSpace) 2 → U :=
      fun x => ⟨B.map x.val, hBU ⟨x.val, x.property, rfl⟩⟩
    have hf : IsOpenEmbedding f := by
      apply IsOpenEmbedding.of_comp _ hU.isOpenEmbedding_subtypeVal
      exact B.open_embedding
    let e := (regionPartialDiffeomorph E hU hV).toOpenPartialHomeomorph.toHomeomorphSourceTarget
    exact hV.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hf)

/-- The transported forward chart has precisely the displayed pointwise composition. -/
theorem transportSurgeryBallRegion_map (x : StandardCapSpace) :
    (transportSurgeryBallRegion B E hU hV hBU).map x = E.map (B.map x) := rfl

/-- The transported inverse retains the original ball inverse and region inverse. -/
theorem transportSurgeryBallRegion_inverse (y : D.carrier) :
    (transportSurgeryBallRegion B E hU hV hBU).inverse y = B.inverse (E.inverse y) := rfl

/-- The transported closed ball is the exact image of the original closed ball. -/
theorem transportSurgeryBallRegion_closedBall :
    (transportSurgeryBallRegion B E hU hV hBU).closedBall = E.map '' B.closedBall := by
  change (E.map ∘ B.map) '' Metric.closedBall 0 1 = E.map '' (B.map '' Metric.closedBall 0 1)
  exact Set.image_comp _ _ _

include hBU in
/-- The original closed ball lies in the source of the actual region equivalence. -/
theorem surgeryBall_closedBall_subset_region : B.closedBall ⊆ U :=
  (surgeryBall_closedBall_subset_image B).trans hBU

/-- The literal region map carries the ball-complement source onto the ball-complement target. -/
theorem transportSurgeryBallRegion_complement_image :
    E.map '' (U \ B.closedBall) = V \ (transportSurgeryBallRegion B E hU hV hBU).closedBall := by
  rw [transportSurgeryBallRegion_closedBall]
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨E.map_image.subset ⟨x, hx.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    have heq : z = x := E.left_inverse.injOn
      (surgeryBall_closedBall_subset_region B hBU hz) hx.1 hzx
    exact hx.2 (heq ▸ hz)
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := E.map_image.symm ▸ hy.1
    refine ⟨x, ⟨hx, ?_⟩, hxy⟩
    intro hxb
    exact hy.2 ⟨x, hxb, hxy⟩

/-- Restriction removes precisely the given ball and its transported image, keeping both maps. -/
noncomputable def transportSurgeryBallRegionComplement :
    SurgeryRegionEquivalence A D (U \ B.closedBall)
      (V \ (transportSurgeryBallRegion B E hU hV hBU).closedBall) where
  map := E.map
  inverse := E.inverse
  map_image := transportSurgeryBallRegion_complement_image B E hU hV hBU
  inverse_image := by
    rw [← transportSurgeryBallRegion_complement_image B E hU hV hBU]
    exact E.left_inverse.image_image' Set.diff_subset
  left_inverse := E.left_inverse.mono Set.diff_subset
  right_inverse := E.right_inverse.mono Set.diff_subset
  map_smooth := E.map_smooth.mono Set.diff_subset
  inverse_smooth := E.inverse_smooth.mono Set.diff_subset

variable (B₀ B₁ : SurgeryBallEmbedding A)
  (hdisjoint : Disjoint (B₀.map '' Metric.ball 0 2) (B₁.map '' Metric.ball 0 2))

include hdisjoint in
/-- The full second ball chart avoids the first actual closed ball. -/
theorem disjoint_ball_image_subset_complement : B₁.map '' Metric.ball 0 2 ⊆ B₀.closedBallᶜ := by
  intro x hx hxb
  exact Set.disjoint_left.mp hdisjoint (surgeryBall_closedBall_subset_image B₀ hxb) hx

/-- Collapsing the first actual ball transports the second ball with its literal coordinates. -/
noncomputable def punctureTransportedSecondBall : SurgeryBallEmbedding A :=
  transportSurgeryBallRegion B₁ (surgeryBallPunctureEquivalence B₀)
    (surgeryBall_closedImage_compact B₀ 1 (by norm_num)).isClosed.isOpen_compl
    isClosed_singleton.isOpen_compl (disjoint_ball_image_subset_complement B₀ B₁ hdisjoint)

/-- The first-ball collapse fixes every point of the whole second ball chart. -/
theorem punctureTransportedSecondBall_map (x : StandardCapSpace)
    (hx : x ∈ Metric.ball 0 2) :
    (punctureTransportedSecondBall B₀ B₁ hdisjoint).map x = B₁.map x := by
  change surgeryBallPatch B₀ punctureCollapse (B₁.map x) = B₁.map x
  apply surgeryBallPatch_of_not_mem
  intro hfirst
  exact Set.disjoint_left.mp hdisjoint hfirst ⟨x, hx, rfl⟩

/-- Its actual closed ball is therefore unchanged by this first-ball collapse. -/
theorem punctureTransportedSecondBall_closedBall :
    (punctureTransportedSecondBall B₀ B₁ hdisjoint).closedBall = B₁.closedBall := by
  apply Set.image_congr
  intro x hx
  exact punctureTransportedSecondBall_map B₀ B₁ hdisjoint x
    (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hx)

/-- The first-ball collapse identifies the complement of both actual closed balls
with the exact punctured complement of the transported second ball. -/
noncomputable def twoBallPunctureRegionEquivalence :
    SurgeryRegionEquivalence A A (B₀.closedBallᶜ \ B₁.closedBall)
      (({B₀.map 0} : Set A.carrier)ᶜ \ (punctureTransportedSecondBall B₀ B₁ hdisjoint).closedBall) :=
  transportSurgeryBallRegionComplement B₁ (surgeryBallPunctureEquivalence B₀)
    (surgeryBall_closedImage_compact B₀ 1 (by norm_num)).isClosed.isOpen_compl
    isClosed_singleton.isOpen_compl (disjoint_ball_image_subset_complement B₀ B₁ hdisjoint)

end PoincareMT.M38
