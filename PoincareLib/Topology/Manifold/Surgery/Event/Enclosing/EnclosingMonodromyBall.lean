import PoincareLib.Topology.Manifold.NeckCap.Models
import PoincareLib.Topology.Manifold.Surgery.Event.Enclosing.EnclosingBallSubregions
import PoincareLib.Topology.Manifold.Surgery.Event.Reciprocal.ReciprocalSphereBall
import PoincareLib.Topology.Manifold.Surgery.Event.Sphere.SphereMonodromyComparison

/-!
# The actual outer ball in the monodromy model of an enclosing neighborhood

The explicit opposite sphere ball lies away from both supplied holes.
Transporting it through the actual cylinder comparison gives a literal
ball in the monodromy bundle. Its complement is precisely the inner
two-hole region together with the restored zero fiber.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A : GeneralizedSliceCarrier.{u}} (C : SurgeryBallEmbedding A)
  (p : sphereCarrier.{u}.carrier) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (B₀ B₁ : SurgeryBallEmbedding A)
  (hB₀ : B₀.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)
  (hB₁ : B₁.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)

local notation "D₀" => enclosingSphereBall B₀ C p ha ha8 hB₀
local notation "D₁" => enclosingSphereBall B₁ C p ha ha8 hB₁

/-- The two transported closed balls have an open complement in their actual sphere carrier. -/
theorem enclosingSphereTwoBallComplement_open : IsOpen ((D₀).closedBall ∪ (D₁).closedBall)ᶜ :=
  ((surgeryBall_closedImage_compact D₀ 1 (by norm_num)).isClosed.union
    (surgeryBall_closedImage_compact D₁ 1 (by norm_num)).isClosed).isOpen_compl

/-- The entire explicit opposite chart avoids both original transported holes. -/
theorem reciprocalSphereBall_subset_twoBallComplement :
    (reciprocalSphereBall p ha ha8).map '' Metric.ball 0 2 ⊆
      ((D₀).closedBall ∪ (D₁).closedBall)ᶜ := by
  intro y hy hbad
  have hdis := Set.disjoint_left.mp (reciprocalSphereBall_full_disjoint p ha ha8) hy
  rcases hbad with hbad | hbad
  · exact hdis (enclosingSphereBall_inside_unit B₀ C p ha ha8 hB₀
      (surgeryBall_closedBall_subset_image D₀ hbad))
  · exact hdis (enclosingSphereBall_inside_unit B₁ C p ha ha8 hB₁
      (surgeryBall_closedBall_subset_image D₁ hbad))

-- Section binders must expose their dependencies without local notation.
variable
  (H : @OpenCylinderModel (sphereCarrier.{u}).carrier
    (sphereCarrier.{u}).topologicalSpace (sphereCarrier.{u}).chartedSpace
      ((enclosingSphereBall B₀ C p ha ha8 hB₀).closedBall ∪
        (enclosingSphereBall B₁ C p ha ha8 hB₁).closedBall)ᶜ)
  (beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

/-- The original monodromy zero-fiber complement is open in the lifted carrier. -/
theorem monodromyLiftedZeroFiber_complement_open :
    IsOpen ((monodromyLiftedZeroFiber.{u} beta)ᶜ) := by
  rw [← monodromyLiftedCollar_central beta (1 / 4) (by norm_num)]
  exact (comparisonCentral_isClosed (monodromyLiftedCollar beta (1 / 4) (by norm_num))
    (by norm_num : (0 : ℝ) < 1 / 4) rfl).isOpen_compl

/-- The original outer sphere chart transported through the actual cylinder coordinates. -/
noncomputable def enclosingMonodromyBall : SurgeryBallEmbedding (monodromyCarrier.{u} beta) :=
  transportSurgeryBallRegion
    (A := sphereCarrier.{u}) (D := monodromyCarrier.{u} beta)
    (U := ((D₀).closedBall ∪ (D₁).closedBall)ᶜ)
    (V := (monodromyLiftedZeroFiber.{u} beta)ᶜ)
    (reciprocalSphereBall p ha ha8)
    (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta)
    (enclosingSphereTwoBallComplement_open C p ha ha8 B₀ B₁ hB₀ hB₁)
    (monodromyLiftedZeroFiber_complement_open beta)
    (reciprocalSphereBall_subset_twoBallComplement C p ha ha8 B₀ B₁ hB₀ hB₁)

/-- Its total forward map retains the original opposite chart and actual quotient coordinates. -/
theorem enclosingMonodromyBall_map (x : StandardCapSpace) :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).map x =
      (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map
        ((reciprocalSphereBall p ha ha8).map x) := rfl

/-- Its actual removed closed ball is the exact image under the original cylinder comparison. -/
theorem enclosingMonodromyBall_closedBall :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).closedBall =
      (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map ''
        (reciprocalSphereBall p ha ha8).closedBall :=
  transportSurgeryBallRegion_closedBall _ _ _ _ _

/-- The transported closed ball is wholly away from the actual zero fiber. -/
theorem enclosingMonodromyBall_avoids_zero :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).closedBall ⊆
      (monodromyLiftedZeroFiber beta)ᶜ := by
  rw [enclosingMonodromyBall_closedBall]
  rintro _ ⟨x, hx, rfl⟩
  exact (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map_image.subset ⟨x,
    reciprocalSphereBall_subset_twoBallComplement C p ha ha8 B₀ B₁ hB₀ hB₁
      (surgeryBall_closedBall_subset_image (reciprocalSphereBall p ha ha8) hx), rfl⟩

/-- Removing the explicit outer ball from the two-hole sphere leaves the actual inner region. -/
theorem enclosingSphere_innerTwoHole_eq :
    ((D₀).closedBall ∪ (D₁).closedBall)ᶜ \ (reciprocalSphereBall p ha ha8).closedBall =
      enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ := by
  change ((D₀).closedBall ∪ (D₁).closedBall)ᶜ ∩ (reciprocalSphereBall p ha ha8).closedBallᶜ =
    ((spherePoleReferenceBall p).map '' Metric.ball 0 (3 / 2)) ∩
      ((D₀).closedBall ∪ (D₁).closedBall)ᶜ
  rw [reciprocalSphereBall_complement, Set.inter_comm]

/-- The precise punctured monodromy ball is the actual inner two-hole image with its zero fiber restored. -/
theorem enclosingMonodromyBall_complement :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).closedBallᶜ =
      (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map ''
        enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ ∪
          monodromyLiftedZeroFiber beta := by
  let F := sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta
  let D := enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta
  have hdiff : F.map '' enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ =
      (monodromyLiftedZeroFiber beta)ᶜ \ D.closedBall := by
    rw [← enclosingSphere_innerTwoHole_eq C p ha ha8 B₀ B₁ hB₀ hB₁]
    exact transportSurgeryBallRegion_complement_image (reciprocalSphereBall p ha ha8) F
      (enclosingSphereTwoBallComplement_open C p ha ha8 B₀ B₁ hB₀ hB₁)
      (monodromyLiftedZeroFiber_complement_open beta)
      (reciprocalSphereBall_subset_twoBallComplement C p ha ha8 B₀ B₁ hB₀ hB₁)
  ext y
  constructor
  · intro hy
    by_cases hz : y ∈ monodromyLiftedZeroFiber beta
    · exact Or.inr hz
    · exact Or.inl (hdiff.symm ▸ ⟨hz, hy⟩)
  · rintro (hy | hy)
    · exact (hdiff.subset hy).2
    · exact fun hD => enclosingMonodromyBall_avoids_zero C p ha ha8 B₀ B₁ hB₀ hB₁ H beta hD hy

end PoincareMT.M38
