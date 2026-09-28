import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Finite
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Path.Comparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set

universe u

namespace PoincareConjecture

open Poincare.RicciFlow.Harnack

theorem differentialHarnackAncientTheory_of_hamilton_diagonal
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hdiag :
      ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ T₀ T₁ : ℝ, T₀ < T₁ →
        ∀ F : RicciFlow n M (Ioo T₀ T₁),
        (∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t)) →
        (∀ t ∈ Ioo T₀ T₁, ∀ x : M,
          LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
        (∀ t ∈ Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
          ∀ x : M, LeviCivitaData.CurvatureOperatorBound
            (F.connection t) K x) →
        ∀ t ∈ Ioo T₀ T₁, ∀ x : M,
          ∀ v : TangentSpace (𝓡 n) x, ∀ i,
          0 ≤ hamiltonM (F.connection t) (t - T₀) x
              ((F.metric t).orthonormalBasis x i)
              ((F.metric t).orthonormalBasis x i) +
            2 * hamiltonP (F.connection t) x v
              ((F.metric t).orthonormalBasis x i)
              ((F.metric t).orthonormalBasis x i) +
            (F.connection t).curvatureTensor x v
              ((F.metric t).orthonormalBasis x i) v
              ((F.metric t).orthonormalBasis x i)) :
    HarnackAncientTheory.{u} := by
  apply Poincare.Geometry.RicciFlow.Harnack.assemble_harnack_from_finite_differential
    hM04
  intro n M _ _ _ _ _ _ T₀ T₁ hT F hcomplete hcurv hbound
  apply finite_differential_of_hamilton_diagonal hM04 T₀ T₁ F
  intro t ht x v
  exact hdiag n M T₀ T₁ hT F hcomplete hcurv hbound t ht x v

theorem differentialHarnackAncientTheory_of_hamilton_block
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hblock :
      ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ T₀ T₁ : ℝ, T₀ < T₁ →
        ∀ F : RicciFlow n M (Ioo T₀ T₁),
        (∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t)) →
        (∀ t ∈ Ioo T₀ T₁, ∀ x : M,
          LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
        (∀ t ∈ Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
          ∀ x : M, LeviCivitaData.CurvatureOperatorBound
            (F.connection t) K x) →
        ∀ t ∈ Ioo T₀ T₁, ∀ x : M,
          HamiltonBlockPos F t x (t - T₀)) :
    HarnackAncientTheory.{u} := by
  apply Poincare.Geometry.RicciFlow.Harnack.assemble_harnack_from_finite_differential
    hM04
  intro n M _ _ _ _ _ _ T₀ T₁ hT F hcomplete hcurv hbound
  apply finite_differential_of_hamilton_block hM04 T₀ T₁ F
  intro t ht x
  exact hblock n M T₀ T₁ hT F hcomplete hcurv hbound t ht x

end PoincareConjecture
