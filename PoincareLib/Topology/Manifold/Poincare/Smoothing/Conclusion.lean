import PoincareLib.Topology.Manifold.Poincare.Smoothing.Basic

/-!
# M76 compatible smoothing bridge

The primitive input is a compact connected topological three-manifold.  The
output is a homeomorphic smooth model with its own atlas.  Hamilton 1976 and
Cairns 1940 are the source results; no Poincare endpoint is part of this
definition.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

def M76SmoothingConclusion {M : Type u} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M)) : Prop :=
  Nonempty (SmoothingBridgeConclusion P)

end PoincareMT
