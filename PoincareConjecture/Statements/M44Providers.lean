import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M44CapPersistencePredecessors : Prop where
  curvature : RicciFlowCurvatureTheory.{u}
  ordinary_flow : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
    Nonempty (OrdinaryParabolicRescaling F Q hQ a)

end PoincareConjecture
