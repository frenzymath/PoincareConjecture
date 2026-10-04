import PoincareLib.Geometry.CurveShortening.Comparison.Assembly
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Evolution
import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Comparison

/-! Assembly of all original M64 clauses on one actual M63 geometry.
Source: MT Chapter 19, Lemmas 19.15 and 19.31, Proposition 19.35 and
the compact-family constructions on pp. 449-462. -/

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- The actual M63 geometry supports all M64 flow fields, including the original
small-annulus ramp comparison. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16,
pp. 447-449; Lemma 19.31, pp. 462 and 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
def m64FlowConclusion_of_M63_analytic
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Icc a b)}
    (G : M63AmbientGeometry F) (analytic : M63AnalyticConclusion F G)
    (hcompact : IsCompact (univ : Set M)) (hn : 3 ≤ n) : M64FlowConclusion F := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  exact m64FlowConclusion_of_fields G
    (m64AnnulusEvolution_of_M63 G analytic hcompact (by omega))
    (m64RampSmallAnnulusComparison_of_geometry G) (m64ProjectionField_of_annulus G)

/-- All frozen M64 conclusions from the exact predecessor service, with
the same chosen geometry retained by the three-dimensional record.
Source: MT Chapter 19, pp. 447-481, and the 2015 correction, pp. 8-9. -/
theorem m64ComparisonTheory_from_M63 (hM63 : M63RampEstimatesTheory.{u}) :
    M64ComparisonTheory.{u} := by
  refine ⟨m64IntrinsicAnnulusComparison, ?_, ?_, ?_⟩
  · intro M _ _ _ _ _ g D hcompact
    exact m64StaticApproximationTheory_of_compact g D hcompact
  · intro n M _ _ _ _ _ a b F hn hcompact
    obtain ⟨C⟩ := hM63.2.1 n M a b F hcompact
    exact ⟨m64FlowConclusion_of_M63_analytic C.geometry C.analytic hcompact hn⟩
  · intro M _ _ _ _ _ a b F hcompact
    obtain ⟨C⟩ := hM63.2.1 3 M a b F hcompact
    let flow := m64FlowConclusion_of_M63_analytic C.geometry C.analytic hcompact (by norm_num)
    exact m64ThreeDimensionalFlowConclusion_of_flow_M63 hM63 hcompact flow C.analytic

end PoincareMT
