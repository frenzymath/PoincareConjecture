import PoincareConjecture.Definitions.Ch06.ReducedLength
import PoincareConjecture.Statements.Ch06.LGeometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

structure ReducedLengthDifferentialTheory {J : Set ℝ}
    (F : RicciFlow n M J) (T τmax : ℝ) [ConnectedSpace M] where
  regular_locus :
    ∀ p : M, ∀ τ : ℝ, 0 < τ → τ < τmax →
      ∃ U : Set M, IsOpen U ∧ Dense U ∧ Set.Nonempty U ∧
        ∀ q ∈ U, Nonempty (ReducedLengthRegularPoint F T τmax p q τ)
  regular_point_formulas :
    ∀ p q : M, ∀ τ : ℝ,
      ∀ r : ReducedLengthRegularPoint F T τmax p q τ,
        deriv (fun s ↦ r.representative (q, s)) τ =
          (F.connection (T - τ)).scalarCurvature q -
            r.representative (q, τ) / τ +
            reducedHarnackIntegral F T r.path.curve
              r.path_scalar_time_derivative τ /
              (2 * τ * Real.sqrt τ) ∧
        reducedLengthGradientNormSq F T r.representative τ q =
          r.representative (q, τ) / τ -
            reducedHarnackIntegral F T r.path.curve
              r.path_scalar_time_derivative τ /
              (τ * Real.sqrt τ) -
            (F.connection (T - τ)).scalarCurvature q ∧
        reducedLengthLaplacian F T r.representative τ q ≤
          (n : ℝ) / (2 * τ) -
            (F.connection (T - τ)).scalarCurvature q -
            reducedHarnackIntegral F T r.path.curve
              r.path_scalar_time_derivative τ /
              (2 * τ * Real.sqrt τ) ∧
        deriv (fun s ↦ r.representative (q, s)) τ +
            reducedLengthLaplacian F T r.representative τ q ≤
          ((n : ℝ) / 2 - r.representative (q, τ)) / τ ∧
        deriv (fun s ↦ r.representative (q, s)) τ -
            reducedLengthLaplacian F T r.representative τ q +
            reducedLengthGradientNormSq F T r.representative τ q -
            (F.connection (T - τ)).scalarCurvature q +
            (n : ℝ) / (2 * τ) ≥ 0 ∧
        2 * reducedLengthLaplacian F T r.representative τ q -
            reducedLengthGradientNormSq F T r.representative τ q +
            (F.connection (T - τ)).scalarCurvature q +
            (r.representative (q, τ) - (n : ℝ)) / τ ≤ 0
  upper_barrier_extension :
    ∀ p q : M, ∀ τ : ℝ, 0 < τ → τ < τmax → ∀ ε : ℝ, 0 < ε →
      ∃ B : ReducedLengthUpperBarrier F T p q τ,
        reducedLengthBarrierResidual F T p q τ B ≤ ε

  exponential_geometry :
    ∀ p : M, Nonempty (LExponentialGeometry F T τmax p)

  local_upper_barrier_bounds :
    ∀ p : M, ∀ z : M × ℝ, z ∈ Set.univ ×ˢ Set.Ioo 0 τmax →
      ∃ N : Set (M × ℝ), IsOpen N ∧ z ∈ N ∧
        N ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ N,
          ∃ B : ReducedLengthUpperBarrier F T p w.1 w.2,
            |deriv (fun s ↦ B.representative (w.1, s)) w.2| ≤ C ∧
            reducedLengthGradientNormSq F T B.representative w.2 w.1 ≤ C ∧
            ∀ v : TangentSpace (𝓡 n) w.1,
              (F.connection (T - w.2)).hessian
                (fun q ↦ B.representative (q, w.2)) w.1 v v ≤
                  C * (F.metric (T - w.2)).inner w.1 v v

  regular_point_equality :
    ∀ p : M, ∀ G : LExponentialGeometry F T τmax p,
      ∀ z : M × ℝ, ∀ hz : z ∈ G.regularImage,
        let r := G.regular_point z hz
        reducedLengthLaplacian F T r.representative z.2 z.1 =
            (n : ℝ) / (2 * z.2) - (F.connection (T - z.2)).scalarCurvature z.1 -
              reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative z.2 /
                (2 * z.2 * Real.sqrt z.2) →
          ∀ v w : TangentSpace (𝓡 n) z.1,
            (F.connection (T - z.2)).ricci z.1 v w +
                (F.connection (T - z.2)).hessian
                  (fun q ↦ r.representative (q, z.2)) z.1 v w =
              (F.metric (T - z.2)).inner z.1 v w / (2 * z.2)

end PoincareConjecture
