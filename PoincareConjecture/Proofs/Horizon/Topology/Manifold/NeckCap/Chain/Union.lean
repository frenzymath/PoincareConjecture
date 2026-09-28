import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain







set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ}


def unionOpen (C : BalancedNeckChain g ε) : Opens M :=
  ⟨⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier,
    isOpen_iUnion fun i => (C.neck i.1).carrier_open⟩

end PoincareConjecture.BalancedNeckChain
