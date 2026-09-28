import PoincareConjecture.Statements.M45ControlledSchedules
import PoincareConjecture.Definitions.M45InitialPrefix
import PoincareConjecture.Proofs.M45.PrefixWitness
import PoincareConjecture.Statements.Ch04.Continuation
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.M27KappaAlternatives
import PoincareConjecture.Statements.M28BoundedDistance
import PoincareConjecture.Statements.M31SingularRegularLimit
import PoincareConjecture.Statements.M32HornSelection
import PoincareConjecture.Proofs.M45.Sec15_2_Constants.Assembly
import PoincareConjecture.Proofs.M45.Sec2_SmallNecks.Prop2_19
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Producer
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Claim15_1_InitialFlow
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.InitialCapture_Uniqueness
import PoincareConjecture.Proofs.M45.Ch9_Models.ModelAnalyticBounds
import PoincareConjecture.Proofs.M45.Ch12_Standard.CapRefinement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem repairedControlledSchedules
    (h03 : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [CompactSpace M], RicciFlowLocalTheory 3 M)
    (h04 : RicciFlowCurvatureTheory.{u})
    (A : RepairedNeckCapTopologyTheory.{u})
    (h27 : RepairedKappaAlternativeTheory.{u})
    (h28 : RepairedBoundedDistanceTheory.{u})
    (h31 : RepairedSingularRegularLimitTheory.{u})
    (h32 : RepairedHornSelectionTheory.{u}) :
    RepairedControlledSchedulesTheory.{u} := by
  have _ := h04
  exact M45.controlledSchedulesOfProducers A h27 h28 h31 h32
    M45.smallNeckThreshold M45.neckGluingProducer
    (M45.initialFlowProducer h03) (M45.initialCaptureProducer h03)
    M45.modelAnalyticBounds M45.capRefinementProducer

end PoincareConjecture
