import PoincareLib.Topology.Manifold.ThreeDimensional.Conclusion
import PoincareLib.Topology.Manifold.ThreeDimensional.Homology.H2
import PoincareLib.Topology.Manifold.ThreeDimensional.Homotopy

/-!
# Closed simply connected three-manifold topology proof assembly

The proof assembles the orientation, manifold-to-CW, Poincare-duality,
Hurewicz, and Whitehead results required by the later extinction path.
Every conclusion is explicit in `ClosedSimplyConnectedThreeManifoldConclusion`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- M02: a compact Hausdorff second-countable simply connected smooth
three-manifold has compatible orientation and CW data, trivial first and
second homotopy groups, third homotopy group isomorphic to the integers, and
a homotopy equivalence with the standard three-sphere.

Sources: Morgan-Tian's discussion after Proposition 18.9, p. 424, and after
Claim 18.20, p. 431. Source provenance and the exact statement review are in
`references/ricci-flow/mapher/m02-topology.md`. -/
theorem closedSimplyConnectedThreeManifoldTopology
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [SimplyConnectedSpace M] :
    Nonempty (ClosedSimplyConnectedThreeManifoldConclusion (M := M)) := by
  exact Poincare.Topology.nonempty_threeManifoldTopologyConclusion_of_integralHomology_two_isZero
    (Poincare.Topology.integralThreeManifoldHomologyTwo_isZero (M := M))

end PoincareMT
