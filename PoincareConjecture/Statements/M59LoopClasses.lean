import PoincareConjecture.Statements.M59LoopIdentification
import PoincareConjecture.Statements.M59ComponentTopology
import PoincareConjecture.Statements.M58LoopSmoothing
import PoincareConjecture.Statements.M40ComparisonHomotopy
import PoincareConjecture.Definitions.M59BasepointTransport

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareConjecture

structure M59ComponentTopologyConclusion : Prop where
  pi_two_obstruction : M59ClosedPiTwoObstructionClaim.{u}
  finite_fundamental_group : M59FiniteFundamentalGroupClaim.{u}
  finite_cover : M59ClosedFiniteCoverClaim.{u}
  noncompact_contractibility : M59NoncompactContractibilityClaim.{u}

def M59ComponentRepresentativeClaim (S : M59IdentificationSystem.{u}) : Prop :=
  ∀ {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (pi_two_trivial : Subsingleton
      (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint))
    (xi : HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint),
    Nonempty (M59WidthCarrierRepresentative C S.quotient.map
      (S.core C.compact C.connected C.basepoint pi_two_trivial).pi_two_pi_three xi)

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

def M59LoopClassesAndComponentTopologyTheory : Prop :=
  ∃ S : M59IdentificationSystem.{u},
    M59ComponentRepresentativeClaim S ∧
      M59ShortLoopPiThreeClaim S ∧
      Nonempty M59HigherBasepointTransportService.{u}

end PoincareConjecture
