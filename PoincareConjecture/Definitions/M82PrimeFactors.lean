import PoincareConjecture.Definitions.M73SphereFactors

















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M82PrimeFactorLedger
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N)
    (C : M72ReconstructionConclusion I)
    (F : M73SphereFactorConclusion I C) where
  source : Fin C.summand_count → M72SummandIndex I C.ledger
  source_bijective : Function.Bijective source
  source_eq : source = C.summand_index
  pieces : Fin C.summand_count → GeneralizedSliceCarrier := C.pieces
  piece_eq : ∀ j,
    pieces j =
      (M72EventTopology I C.ledger (source j).1).conclusion.piece
        (source j).2.1
  non_survivor : ∀ j,
    (M72EventTopology I C.ledger (source j).1).conclusion.kind
      (source j).2.1 ≠ .survivor
  spaceform : ∀ j,
    (M72EventTopology I C.ledger (source j).1).conclusion.kind
      (source j).2.1 = .spaceform
  sphere_map : ∀ j, Diffeomorph (𝓡 3) (𝓡 3) (pieces j).carrier ThreeSphere ∞
  assembly : SmoothFiniteConnectedSumAssembly pieces
    (I.global.certificate.flow.slice 0)

end PoincareConjecture
