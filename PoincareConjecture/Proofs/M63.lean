import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.Profile
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.AmbientGeometry
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.AnalyticAssembly
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FamilyConclusionAssembly
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.Lemma19_17_RawApproximation
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.Lemma19_17_FamilySolutions
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.UniformDerivativeEstimates
import PoincareConjecture.Proofs.M58
import PoincareConjecture.Proofs.M62

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m63SmallLoopFillingService_from_M58 : M63SmallLoopFillingService.{u} :=
  repairedShortLoopTriviality.short_loop.small_loop_filling

theorem m63RampEstimates (hM58 : M63SmallLoopFillingService.{u})
    (hM62 : M62CurveEvolutionTheory.{u}) : M63RampEstimatesTheory.{u} := by
  classical
  have construction : M63SmallLoopFillingService.{u} →
      M62CurveEvolutionTheory.{u} → M63RampEstimatesTheory.{u} := by
    intro _ h62
    have analytic {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
        [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {a b : ℝ} (F : RicciFlow n M (Set.Icc a b))
        (hcompact : IsCompact (Set.univ : Set M)) (G : M63AmbientGeometry F) :
        M63AnalyticConclusion F G := by
      let : CompactSpace M := isCompact_univ_iff.mp hcompact
      apply m63AnalyticConclusion_of_local_uniform F hcompact h62 G
        (M63.localCurveTheory_of_compact F hcompact)
      · intro circumference hcirc
        let : Fact (0 < circumference) := ⟨hcirc⟩
        exact M63.localCurveTheory_of_compact (G.product circumference hcirc).flow isCompact_univ
      · exact m63UniformDerivativeEstimates_of_compact F hcompact h62 G
    refine ⟨fun _ hN => m63ProfileProperties hN, ?_, ?_, ?_⟩
    · intro n M _ _ _ _ _ a b F hcompact
      obtain ⟨G⟩ := m63AmbientGeometry_nonempty (F := F) h62 hcompact
      exact ⟨⟨G, analytic F hcompact G⟩⟩
    · intro M _ _ _ _ _ a b F hcompact G Gamma hnull zeta hzeta _hzeta1
      obtain ⟨A⟩ := m63RawApproximation_nonempty F hcompact Gamma hnull hzeta
      obtain ⟨C⟩ := m63FamilyConclusion_of_solutions G (analytic F hcompact G) A
        (fun circumference hcirc => Classical.choice
          (m63ProductSolutionFamily_nonempty F hcompact h62 G A circumference hcirc))
      exact ⟨C.1⟩
    · intro M _ _ _ _ _ a b F hcompact G Gamma _hnull zeta _hzeta A
      exact m63FamilyConclusion_of_solutions G (analytic F hcompact G) A
        (fun circumference hcirc => Classical.choice
          (m63ProductSolutionFamily_nonempty F hcompact h62 G A circumference hcirc))
  exact construction hM58 hM62

theorem m63RampEstimates_from_predecessors : M63RampEstimatesTheory.{u} :=
  m63RampEstimates m63SmallLoopFillingService_from_M58
    m62CorrectedCurveEvolution_from_predecessors

end PoincareConjecture
