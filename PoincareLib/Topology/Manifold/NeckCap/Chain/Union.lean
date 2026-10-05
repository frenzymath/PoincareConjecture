import PoincareLib.Topology.Manifold.NeckCap.Chain

/-!
# The open union of a balanced neck chain

The actual carriers of the active necks form an open subset of the ambient
manifold, for every finite or infinite chain shape.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareMT.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

/-- The exact union of the active necks, as an open subset of the manifold. -/
def unionOpen (C : BalancedNeckChain g ε) : Opens M :=
  ⟨⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier,
    isOpen_iUnion fun i => (C.neck i.1).carrier_open⟩

end PoincareMT.BalancedNeckChain
