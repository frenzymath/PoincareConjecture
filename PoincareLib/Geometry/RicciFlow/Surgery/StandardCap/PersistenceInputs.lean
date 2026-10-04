import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory

/-!
Adapted from Mapher `PoincareMT/Statements/M44Providers.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M44's analytic predecessor services

M44 applies the actual curvature-calculus service from M04 and the ordinary
parabolic-rescaling service from M13 on the physical Type-`u` carriers of an
observed surgery flow. The cap-persistence theorem owns the compactness,
stopping, and limit construction; this record names only the two reusable
analytic services it genuinely invokes.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure M44CapPersistencePredecessors : Prop where
  curvature : RicciFlowCurvatureTheory.{u}
  ordinary_flow : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
    Nonempty (OrdinaryParabolicRescaling F Q hQ a)

end PoincareMT
