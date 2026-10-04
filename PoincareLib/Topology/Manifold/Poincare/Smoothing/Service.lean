import PoincareLib.Topology.Manifold.Poincare.Smoothing.Conclusion

/-!
# M76 Hamilton--Cairns smoothing statement

Natural-language statement: every compact connected topological 3-manifold
admits a homeomorphic smooth model in the same universe.  The model carries
explicit topology, charts, manifold, compactness and connectedness data, and
the input topological atlas is not treated as a smooth atlas.

Source: Hamilton, The Triangulation of 3-Manifolds, Theorem 2 part 1,
printed p. 64 (proof p. 69), and Cairns, Homeomorphisms Between Topological
Manifolds and Analytic Manifolds, Theorem III, printed p. 797 (proof section
11, p. 807).  See `references/smoothing-source-verification-2026-09-11.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

def M76SmoothingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M)),
    M76SmoothingConclusion P

end PoincareMT
