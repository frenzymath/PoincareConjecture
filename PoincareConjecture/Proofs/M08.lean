import PoincareConjecture.Statements.Ch06.LGeometry
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M08.PathBasics
import PoincareConjecture.Proofs.M08.VariationPaths
import PoincareConjecture.Proofs.M08.PathCongruence
import PoincareConjecture.Proofs.M08.Endpoints
import PoincareConjecture.Proofs.M08.ChartExtensions
import PoincareConjecture.Proofs.M08.RegularizedAction
import PoincareConjecture.Proofs.M08.MetricCompactness
import PoincareConjecture.Proofs.M08.AdmissiblePaths
import PoincareConjecture.Proofs.M08.MinimizerAbstract
import PoincareConjecture.Proofs.M08.CompleteMinimizer
import PoincareConjecture.Proofs.M08.EulerLagrange
import PoincareConjecture.Proofs.M08.RegularizedGeodesic
import PoincareConjecture.Proofs.M08.FirstVariation
import PoincareConjecture.Proofs.M08.IndexKernel
import PoincareConjecture.Proofs.M08.ExtensionToZero
import PoincareConjecture.Proofs.M08.SecondVariation
import PoincareConjecture.Proofs.M08.JacobiInitialValue

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem lGeodesicExistenceAndVariation
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    Nonempty (LGeodesicTheory F T τmax) := by
  refine ⟨{
    minimizing_existence := ?_
    euler_lagrange := ?_
    regularized_geodesic := ?_
    first_variation := ?_
    second_variation_jacobi := ?_
    extension_to_zero := ?_
    reduced_length_attained := ?_
    second_variation := ?_
    jacobi_initial_value := ?_
  }⟩
  · intro τ₁ τ₂ hτ₁ hordered hτ₂ p₁ p₂
    exact M08.exists_minimizing_backward_path hM04 hT hwindow hcurvature hτ₁ hordered hτ₂ p₁ p₂
  · intro τ₁ τ₂ _ _ hτ₂ p hp
    exact M08.isBackwardLGeodesic_of_minimizing hM04 hwindow hcurvature hτ₂ p hp
  · intro τ₁ τ₂ _ _ hτ₂ p hp
    exact M08.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hp
  · intro τ₁ τ₂ _ _ hτ₂ p V
    exact M08.exists_firstVariation hM04 hwindow hτ₂ V
  · intro τ₁ τ₂ _ _ hτ₂ p hp V
    have hEuler := M08.isBackwardLGeodesic_of_minimizing hM04 hwindow hcurvature hτ₂ p hp
    obtain ⟨R⟩ := M08.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hEuler
    exact M08.exists_fixedEndpointSecondVariation hM04 hp R V
  · intro τ₁ τ₂ hτ₁ _ hτ₂ p hp
    exact M08.exists_backward_geodesic_extension hM04 hwindow hcurvature hτ₁ hτ₂ p hp
  · intro τ hτ hτmax p q
    exact M08.reducedLength_attained_of_exists_minimizing
      (M08.exists_minimizing_backward_path hM04 hT hwindow hcurvature le_rfl hτ hτmax p q)
  · intro τ₁ τ₂ _ _ hτ₂ p hp V
    obtain ⟨R⟩ := M08.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hp
    exact M08.exists_secondVariation hM04 V R
  · intro τ₁ τ₂ _ _ _ p R Z
    exact M08.exists_lJacobi_initialValue F hM04 p R Z

theorem lGeodesicExistenceAndVariation_from_M04
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)) :
    Nonempty (LGeodesicTheory F T τmax) := by
  exact lGeodesicExistenceAndVariation F T τmax hT hτmax hwindow hcurvature
    ricciFlowCurvatureTheory

end PoincareConjecture
