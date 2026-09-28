import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CurvatureSupremum
import PoincareConjecture.Statements.M63RampEstimates













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture





theorem m64CurvatureFields_of_M63
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
    (hM63 : M63RampEstimatesTheory.{u})
    (hcompact : IsCompact (Set.univ : Set M)) :
    ∃ _G : M63AmbientGeometry F,
      (∀ t ∈ Set.Icc a b,
        BddAbove (Set.range (fun x : M =>
          (F.connection t).curvatureTensorNorm x))) ∧
      (∀ t ∈ Set.Icc a b, 0 ≤ m64CurvatureSupremum F t) ∧
      ContinuousOn (m64CurvatureSupremum F) (Set.Icc a b) := by
  obtain ⟨C⟩ := hM63.2.1 n M a b F hcompact
  refine ⟨C.geometry, ?_, ?_, ?_⟩
  · intro t ht
    exact m64CurvatureRange_bddAbove_of_compact hcompact ht
  · intro t ht
    exact m64CurvatureSupremum_nonneg
      (m64CurvatureRange_bddAbove_of_compact hcompact ht)
  · exact m64CurvatureSupremum_continuous_of_compact hcompact

end PoincareConjecture
