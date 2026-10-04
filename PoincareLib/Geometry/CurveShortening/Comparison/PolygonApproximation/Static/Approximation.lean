import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Uniform.CompactApproximation
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Uniform.RawFamily
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Static.TheoryAssembly

/-!
# The closed static approximation theory

The pointwise polygon construction and the two uniform all-count producers
fill the frozen static record on a compact smooth Riemannian three-manifold.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Construct the complete static approximation theory on the supplied compact target.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64StaticApproximationTheory_of_compact
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M)) :
    M64StaticApproximationTheory g D :=
  m64StaticApproximationTheory_of_suppliers hcompact
    (fun X hX _zeta hzeta => m64_uniform_compact_approximation g D hcompact X hX hzeta)
    (fun Gamma hnull _zeta hzeta => m64_uniform_raw_family g D hcompact Gamma hnull hzeta)

end PoincareMT
