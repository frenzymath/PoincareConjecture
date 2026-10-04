import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.CompleteMinimizer
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Regularity.EulerLagrange
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Regularity.RegularizedGeodesic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.FirstVariation
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.Index.IndexKernel
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Continuation.ExtensionToZero
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariation
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.JacobiInitialValue

/-!
# Existence and variation of L-geodesics

This is the ordinary-flow M08 entry point.  The complete analytic proof uses
the compactness and variation producers below the reduced-length namespace;
the public declaration keeps the reviewed predecessor package explicit.

Adapted from Mapher `PoincareMT/Proofs/M08.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.
Sources: Morgan-Tian Definitions 6.1-6.2, p. 106; Lemmas 6.4 and 6.8,
pp. 107-108; Lemmas 6.10/6.12 and Proposition 6.13, pp. 109-112;
Proposition 6.33 and Claim 6.34, pp. 120-122; Lemmas 7.2-7.3, pp. 150-151.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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
    exact LGeometry.exists_minimizing_backward_path
      hM04 hT hwindow hcurvature hτ₁ hordered hτ₂ p₁ p₂
  · intro τ₁ τ₂ _ _ hτ₂ p hp
    exact LGeometry.isBackwardLGeodesic_of_minimizing hM04 hwindow hcurvature hτ₂ p hp
  · intro τ₁ τ₂ _ _ hτ₂ p hp
    exact LGeometry.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hp
  · intro τ₁ τ₂ _ _ hτ₂ p V
    exact LGeometry.exists_firstVariation hM04 hwindow hτ₂ V
  · intro τ₁ τ₂ _ _ hτ₂ p hp V
    have hEuler := LGeometry.isBackwardLGeodesic_of_minimizing hM04 hwindow hcurvature hτ₂ p hp
    obtain ⟨R⟩ := LGeometry.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hEuler
    exact LGeometry.exists_fixedEndpointSecondVariation hM04 hp R V
  · intro τ₁ τ₂ hτ₁ _ hτ₂ p hp
    exact LGeometry.exists_backward_geodesic_extension hM04 hwindow hcurvature hτ₁ hτ₂ p hp
  · intro τ hτ hτmax p q
    exact LGeometry.reducedLength_attained_of_exists_minimizing
      (LGeometry.exists_minimizing_backward_path hM04 hT hwindow hcurvature le_rfl hτ hτmax p q)
  · intro τ₁ τ₂ _ _ hτ₂ p hp V
    obtain ⟨R⟩ := LGeometry.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hp
    exact LGeometry.exists_secondVariation hM04 V R
  · intro τ₁ τ₂ _ _ _ p R Z
    exact LGeometry.exists_lJacobi_initialValue F hM04 p R Z

end PoincareMT
