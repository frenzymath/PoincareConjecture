import PoincareLib.Topology.Manifold.Poincare.Smooth.Input
import PoincareLib.Topology.Manifold.Poincare.Statement

/-! Adapted from Mapher `PoincareMT/Statements/M75SmoothPoincare.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M75 smooth endpoint statement

Natural-language theorem statement: if the preceding global-flow and
connected-sum milestones provide, for every compact simply connected smooth
three-manifold, a normalized initial metric, an actual M52 flow certificate,
and an M74 reduction of its time-zero carrier to `ThreeSphere`, then composing
the two concrete diffeomorphisms proves Smooth Poincare.  The input service is
an upstream producer boundary; it contains no endpoint proposition or
preassembled original-to-sphere identification.

Source: Morgan--Tian Corollary 0.2(a), with the initial identification from
Theorem 15.9/Corollary 15.10 and the finite connected-sum reduction from
Corollary 15.4(2); see `references/derived/MT2007.txt:17861-17902` and
`references/derived/MT2007.txt:20386-20442`.
-/

set_option autoImplicit false

universe u

open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT

def M75SmoothPoincareStatement : Prop :=
  ∀ (_hService : ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SimplyConnectedSpace M],
    ∃ N : NormalizedInitialMetric (M := M),
      Nonempty (M75EndpointInput N)),
    SmoothPoincare.{u}

end PoincareMT
