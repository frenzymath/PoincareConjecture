import PoincareLib.Topology.Manifold.NeckCap.Models
import PoincareLib.Topology.Manifold.Surgery.Event.Sphere.SpherePunctureCoordinates
import PoincareLib.Topology.Manifold.Surgery.Event.Monodromy.MonodromyLiftedCollar

/-!
# The two-ball sphere cylinder in its literal monodromy carrier

Fix the original sphere carrier and both balls before specializing the
cylinder comparison. The maps are exactly those of the existing comparison.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (B₀ B₁ : SurgeryBallEmbedding sphereCarrier.{u})
  (H : @OpenCylinderModel (sphereCarrier.{u}).carrier
    (sphereCarrier.{u}).topologicalSpace (sphereCarrier.{u}).chartedSpace
    (B₀.closedBall ∪ B₁.closedBall)ᶜ)
  (beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

/-- The supplied two-ball cylinder identifies its exact complement with
the original zero-fiber complement in the monodromy bundle. -/
noncomputable def sphereTwoBallMonodromyComparison :
    SurgeryRegionEquivalence sphereCarrier.{u} (monodromyCarrier.{u} beta)
      (B₀.closedBall ∪ B₁.closedBall)ᶜ (monodromyLiftedZeroFiber beta)ᶜ :=
  @monodromyCylinderRegionEquivalence.{u} beta sphereCarrier.{u}
    (B₀.closedBall ∪ B₁.closedBall)ᶜ H

/-- The specialization keeps the original comparison definitionally. -/
theorem sphereTwoBallMonodromyComparison_eq :
    sphereTwoBallMonodromyComparison B₀ B₁ H beta =
      @monodromyCylinderRegionEquivalence.{u} beta sphereCarrier.{u}
        (B₀.closedBall ∪ B₁.closedBall)ᶜ H := rfl

/-- Its forward map retains the literal original cylinder coordinates. -/
theorem sphereTwoBallMonodromyComparison_map (x : sphereCarrier.{u}.carrier) :
    (sphereTwoBallMonodromyComparison B₀ B₁ H beta).map x =
      monodromyLiftedCylinder beta (H.inverse x) := rfl

end PoincareMT.M38
