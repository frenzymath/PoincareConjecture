import PoincareLib.Topology.Manifold.Surgery.Event.Enclosing.EnclosingBallSphere

/-!
# Exact inner two-hole regions of the actual enclosing chart

The radius-three-halves neighborhood is compared through the original
enclosing and sphere charts. Removing the two original closed balls
retains the same total maps and gives exactly the corresponding holes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A : GeneralizedSliceCarrier.{u}} (C : SurgeryBallEmbedding A)
  (p : sphereCarrier.{u}.carrier)

/-- The original chart comparison carries precisely the radius-three-halves open ball. -/
theorem enclosingBallSphereCoordinates_inner_image :
    (enclosingBallSphereCoordinates C p).map '' (C.map '' Metric.ball 0 (3 / 2)) =
      (spherePoleReferenceBall p).map '' Metric.ball 0 (3 / 2) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [enclosingBallSphereCoordinates_chart C p
      (Metric.ball_subset_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hz)]
    exact ⟨z, hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨C.map z, ⟨z, hz, rfl⟩, enclosingBallSphereCoordinates_chart C p
      (Metric.ball_subset_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hz)⟩

variable {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (B₀ B₁ : SurgeryBallEmbedding A)
  (hB₀ : B₀.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)
  (hB₁ : B₁.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)

/-- The actual inner two-hole region in the enclosing carrier. -/
def enclosingInnerTwoHoleRegion : Set A.carrier :=
  (C.map '' Metric.ball 0 (3 / 2)) \ (B₀.closedBall ∪ B₁.closedBall)

/-- The exact corresponding inner two-hole region in the reference sphere. -/
def enclosingSphereInnerTwoHoleRegion : Set sphereCarrier.{u}.carrier :=
  ((spherePoleReferenceBall p).map '' Metric.ball 0 (3 / 2)) \
    ((enclosingSphereBall B₀ C p ha ha8 hB₀).closedBall ∪
      (enclosingSphereBall B₁ C p ha ha8 hB₁).closedBall)

/-- The original comparison maps the actual inner region onto exactly its two-hole sphere image. -/
theorem enclosingSphere_innerTwoHole_image :
    (enclosingBallSphereCoordinates C p).map '' enclosingInnerTwoHoleRegion C B₀ B₁ =
      enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ := by
  unfold enclosingSphereInnerTwoHoleRegion enclosingInnerTwoHoleRegion
  rw [enclosingSphereBall_closedBall, enclosingSphereBall_closedBall, ← Set.image_union]
  let E := enclosingBallSphereCoordinates C p
  have hballs : B₀.closedBall ∪ B₁.closedBall ⊆ C.map '' Metric.ball 0 2 :=
    Set.union_subset (enclosingOriginalBall_inside_chart B₀ C hB₀)
      (enclosingOriginalBall_inside_chart B₁ C hB₁)
  have hsmall : C.map '' Metric.ball 0 (3 / 2) ⊆ C.map '' Metric.ball 0 2 :=
    Set.image_mono (Metric.ball_subset_ball (by norm_num))
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨(enclosingBallSphereCoordinates_inner_image C p).subset ⟨x, hx.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    have heq : z = x := E.left_inverse.injOn (hballs hz) (hsmall hx.1) hzx
    exact hx.2 (heq ▸ hz)
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := (enclosingBallSphereCoordinates_inner_image C p).symm ▸ hy.1
    refine ⟨x, ⟨hx, ?_⟩, hxy⟩
    intro hxb
    exact hy.2 ⟨x, hxb, hxy⟩

/-- The inner source is open in the original enclosing carrier. -/
theorem enclosingInnerTwoHoleRegion_open : IsOpen (enclosingInnerTwoHoleRegion C B₀ B₁) :=
  (surgeryBall_image_ball_open C (3 / 2) (by norm_num)).sdiff
    ((surgeryBall_closedImage_compact B₀ 1 (by norm_num)).isClosed.union
      (surgeryBall_closedImage_compact B₁ 1 (by norm_num)).isClosed)

/-- The exact sphere two-hole target is open in the original sphere carrier. -/
theorem enclosingSphereInnerTwoHoleRegion_open :
    IsOpen (enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁) :=
  (surgeryBall_image_ball_open (spherePoleReferenceBall p) (3 / 2) (by norm_num)).sdiff
    ((surgeryBall_closedImage_compact (enclosingSphereBall B₀ C p ha ha8 hB₀)
      1 (by norm_num)).isClosed.union
      (surgeryBall_closedImage_compact (enclosingSphereBall B₁ C p ha ha8 hB₁)
        1 (by norm_num)).isClosed)

/-- The exact inner two-hole equivalence retains both original total chart maps. -/
noncomputable def enclosingSphereInnerTwoHoleEquivalence :
    SurgeryRegionEquivalence A sphereCarrier.{u} (enclosingInnerTwoHoleRegion C B₀ B₁)
      (enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁) := by
  let E := enclosingBallSphereCoordinates C p
  have hsource : enclosingInnerTwoHoleRegion C B₀ B₁ ⊆ C.map '' Metric.ball 0 2 :=
    Set.sdiff_subset.trans (Set.image_mono (Metric.ball_subset_ball (by norm_num)))
  have htarget : enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ ⊆
      (spherePoleReferenceBall p).map '' Metric.ball 0 2 :=
    Set.sdiff_subset.trans (Set.image_mono (Metric.ball_subset_ball (by norm_num)))
  exact {
    map := E.map
    inverse := E.inverse
    map_image := enclosingSphere_innerTwoHole_image C p ha ha8 B₀ B₁ hB₀ hB₁
    inverse_image := by
      rw [← enclosingSphere_innerTwoHole_image C p ha ha8 B₀ B₁ hB₀ hB₁]
      exact E.left_inverse.image_image' hsource
    left_inverse := E.left_inverse.mono hsource
    right_inverse := E.right_inverse.mono htarget
    map_smooth := E.map_smooth.mono hsource
    inverse_smooth := E.inverse_smooth.mono htarget }

/-- The restricted forward map is exactly the original enclosing-to-sphere comparison. -/
theorem enclosingSphereInnerTwoHoleEquivalence_map (x : A.carrier) :
    (enclosingSphereInnerTwoHoleEquivalence C p ha ha8 B₀ B₁ hB₀ hB₁).map x =
      (enclosingBallSphereCoordinates C p).map x := rfl

/-- The restricted inverse likewise retains the actual sphere-to-enclosing comparison. -/
theorem enclosingSphereInnerTwoHoleEquivalence_inverse (y : sphereCarrier.{u}.carrier) :
    (enclosingSphereInnerTwoHoleEquivalence C p ha ha8 B₀ B₁ hB₀ hB₁).inverse y =
      (enclosingBallSphereCoordinates C p).inverse y := rfl

end PoincareMT.M38
