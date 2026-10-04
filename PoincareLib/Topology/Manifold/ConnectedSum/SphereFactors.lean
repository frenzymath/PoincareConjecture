import PoincareLib.Topology.Manifold.ConnectedSum.Reconstruction
import PoincareLib.Topology.Manifold.Poincare.Statement

/-! Adapted from Mapher `PoincareMT/Definitions/M73SphereFactors.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M73 sphere identification of the actual reconstruction factors

Every factor is the event piece selected by M72's bijective ledger. The
conclusion rules out sphere bundles and identifies each remaining positive
spaceform with the unit three-sphere. It contains no identification of the
original manifold or reduction of its connected-sum assembly.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

structure M73SphereFactorConclusion
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (C : M72ReconstructionConclusion I) where
  factor_kind : ∀ j : Fin C.summand_count,
    (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.kind
      (C.summand_index j).2.1 = .spaceform
  factor_sphere : ∀ j : Fin C.summand_count,
    Diffeomorph (𝓡 3) (𝓡 3) (C.pieces j).carrier ThreeSphere ∞

end PoincareMT
