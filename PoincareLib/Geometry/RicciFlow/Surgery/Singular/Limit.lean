import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry

/-!
Adapted from Mapher `PoincareMT/Definitions/M31SingularRegularLimit.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M31 repaired singular-time regular-limit data

The source-aligned conclusion is the complete `SingularLimitConclusion` from
Chapter 11. Reusing that record retains the actual old-time gluing map,
terminal slice, proper scalar curvature, end controls, and canonical
neighborhood output; in particular, an empty regular-limit set remains
allowed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

/-- Terminal regular-limit output for one singular-time assumption. This is
the complete source record, including the gluing compatibility that connects
the terminal source map to the preterminal flow. -/
abbrev RepairedSingularRegularLimitData
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions F T M) := SingularLimitConclusion H

end PoincareMT
