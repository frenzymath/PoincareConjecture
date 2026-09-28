import PoincareConjecture.Proofs.M64.Assembly
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Lemma19_15_Evolution
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.Lemma19_31_Comparison





noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture





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

end PoincareConjecture
