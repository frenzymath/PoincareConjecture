import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M58
import PoincareConjecture.Proofs.M60.Providers
import PoincareConjecture.Proofs.M60.AreaCore
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Minimizer
import PoincareConjecture.Statements.M60Area

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem m60AreaAndFilling
    (P04 : RicciFlowCurvatureTheory.{u})
    (P58 : RepairedShortLoopTrivialityTheory.{u}) :
    M60AreaTheory.{u} := by
  have core :
      (∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus) →
      (∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (J : Set ℝ) (F : RicciFlow n M J),
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
          (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)) →
      M60AreaCore.{u} := by
    intro tensor scalar
    exact m60AreaCore_of_leastSphere tensor scalar m60LeastSphere_of_suProducers
  exact { toM60AreaCore := core P04.tensor_calculus P04.scalar_regular
          short_loop := m60ShortLoopAreaClaim_from_M58 P58 }

theorem m60AreaAndFilling_from_predecessors : M60AreaTheory.{u} :=
  m60AreaAndFilling ricciFlowCurvatureTheory repairedShortLoopTriviality

end PoincareConjecture
