import PoincareConjecture.Proofs.M38.SpherePunctureCoordinates
import PoincareConjecture.Proofs.M38.MonodromyLiftedCollar

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (B₀ B₁ : SurgeryBallEmbedding sphereCarrier.{u})
  (H : @OpenCylinderModel (sphereCarrier.{u}).carrier
    (sphereCarrier.{u}).topologicalSpace (sphereCarrier.{u}).chartedSpace
    (B₀.closedBall ∪ B₁.closedBall)ᶜ)
  (beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

noncomputable def sphereTwoBallMonodromyComparison :
    SurgeryRegionEquivalence sphereCarrier.{u} (monodromyCarrier.{u} beta)
      (B₀.closedBall ∪ B₁.closedBall)ᶜ (monodromyLiftedZeroFiber beta)ᶜ :=
  @monodromyCylinderRegionEquivalence.{u} beta sphereCarrier.{u}
    (B₀.closedBall ∪ B₁.closedBall)ᶜ H

theorem sphereTwoBallMonodromyComparison_eq :
    sphereTwoBallMonodromyComparison B₀ B₁ H beta =
      @monodromyCylinderRegionEquivalence.{u} beta sphereCarrier.{u}
        (B₀.closedBall ∪ B₁.closedBall)ᶜ H := rfl

theorem sphereTwoBallMonodromyComparison_map (x : sphereCarrier.{u}.carrier) :
    (sphereTwoBallMonodromyComparison B₀ B₁ H beta).map x =
      monodromyLiftedCylinder beta (H.inverse x) := rfl

end PoincareConjecture.M38
