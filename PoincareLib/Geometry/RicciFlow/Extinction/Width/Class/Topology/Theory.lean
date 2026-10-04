import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.IdentificationTheory
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Topology.ComponentTheory
import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Theory
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.BasepointTransport

/-!
# M59 loop-class and basepoint-transport contract

One chosen identification system is used by the component representative and
the short-loop conclusion. The only predecessor services are applied M02
closed topology and M58 short-loop triviality, supplied at the proof entry.
The component, metric, point, sphere parameter and represented class remain
explicit. A uniform higher-basepoint transport service is also constructed
for the later changing-component ledger. No width inequality or finite
surgery chronology is asserted here.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareMT

/-- Historical general topology package, retained as an unasserted type.
The Poincare skeleton does not require or admit this package. -/
structure M59ComponentTopologyConclusion : Prop where
  pi_two_obstruction : M59ClosedPiTwoObstructionClaim.{u}
  finite_fundamental_group : M59FiniteFundamentalGroupClaim.{u}
  finite_cover : M59ClosedFiniteCoverClaim.{u}
  noncompact_contractibility : M59NoncompactContractibilityClaim.{u}

/-- Realize the specified class on the actual selected component, using the
same comparison and sphere parameter as the generic loop-space theory. -/
def M59ComponentRepresentativeClaim (S : M59IdentificationSystem.{u}) : Prop :=
  ∀ {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (pi_two_trivial : Subsingleton
      (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint))
    (xi : HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint),
    Nonempty (M59WidthCarrierRepresentative C S.quotient.map
      (S.core C.compact C.connected C.basepoint pi_two_trivial).pi_two_pi_three xi)

/-- M58's uniform threshold, interpreted by the same chosen pi2/pi3
comparison. The family carries the specified class and the same metric. -/
def M59ShortLoopPiThreeClaim (S : M59IdentificationSystem.{u}) : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (g : RiemannianMetric 3 M)
    (compact : IsCompact (Set.univ : Set M))
    (connected : IsConnected (Set.univ : Set M))
    (x : M) (pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 M x)),
    let e := (S.core compact connected x pi_two_trivial).pi_two_pi_three
    ∃ zeta : ℝ, 0 < zeta ∧
      ∀ (xi : HomotopyGroup.Pi 3 M x) (Gamma : FreeTwoSphereFamily (M := M)),
        familySigmaClass Gamma = ⟨x, e.symm xi⟩ →
        (∀ c : LoopTwoSphere, freeLoopLength g (Gamma.family c) < zeta) →
        xi = 1

/-- M59 output on the chosen identification system. The general topology
package above is not an exported obligation; its former inclusion is
superseded by the September 20 Poincare-scope amendment. -/
def M59LoopClassesAndComponentTopologyTheory : Prop :=
  ∃ S : M59IdentificationSystem.{u},
    M59ComponentRepresentativeClaim S ∧
      M59ShortLoopPiThreeClaim S ∧
      Nonempty M59HigherBasepointTransportService.{u}

end PoincareMT
