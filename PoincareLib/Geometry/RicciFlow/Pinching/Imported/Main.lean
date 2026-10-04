import PoincareLib.Geometry.RicciFlow.Pinching.Conclusion
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Pinching.Imported.Compatibility

/-!
# Typed Hamilton--Ivey milestone assembly

The analytic maximum-principle proof is adapted from the published Archon Horizon
workspace commit bdc557369304b0ef899f8c31d3d5fece41eabcb1. Its conclusion retains
the spectral bridge and the full project norm
bound so later milestones need not introduce unreviewed operator data.
-/

/-! M05 is the numbered review and proof entry point. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

namespace PinchingImport

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- M05: for a compact smooth three-dimensional Ricci flow on [a,b), with
0 <= a < b and Hamilton-Ivey pinching at a, the M04 curvature theory implies
pinching at every included time. It also supplies the three-eigenvalue spectral
identities and the derived bound |Rm| <= 13 * max R0 (exp 4) wherever R <= R0.

Sources: Morgan-Tian Theorem 4.32, pp. 79-80, and Claims 4.28/4.30,
pp. 77-79. The numerical full-tensor estimate is a project-derived consequence.
Retain the corrected evolution and eigenvalue-concavity conventions in
`reviews/errata/2026-09-11-tensor-evolution.md`. -/
theorem hamiltonIveyPinching
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : HamiltonIveyPinchedAt (F.connection a) a) :
    HamiltonIveyPinchingConclusion a b F := by
  exact horizon_hamiltonIveyPinching ha hab F hM04 hinit

/-- The M05 result with the reviewed M04 assembly supplied explicitly. -/
theorem hamiltonIveyPinching_from_M04
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hinit : HamiltonIveyPinchedAt (F.connection a) a) :
    HamiltonIveyPinchingConclusion a b F := by
  exact hamiltonIveyPinching ha hab F ricciFlowCurvatureTheory hinit

end PinchingImport

end PoincareMT
