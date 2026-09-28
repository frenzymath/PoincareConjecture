import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CoordinateRealization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.ScalarModulus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.SingularRoundComponent

open SingularRegularLimit.RoundComparison

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)

theorem exists_normalCoordinateRealization (hepsilon : epsilon ≤ 1 / 200)
    (p : N.model.carrier) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) N.model.carrier)
      (g₀ h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (D₀ : LeviCivitaData g₀) (_Dh : LeviCivitaData h)
      (U : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen U ∧ (0 : EuclideanSpace ℝ (Fin 3)) ∈ U ∧ U ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible) ∧
      (∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
        g₀.inner y v w = N.model_metric.inner (e y)
          (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w)) ∧
      (∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
        h.inner y v w = N.normalizedMetric.inner (e y)
          (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w)) ∧
      g₀.euclideanCoefficients 0 = innerSL ℝ ∧
      CoordinateExponential.christoffelBilinear g₀.euclideanCoefficients 0 = 0 ∧
      (∀ j : ℕ, j ≤ 2 → ∀ v : Fin (2 + j) → EuclideanSpace ℝ (Fin 3),
        |D₀.iteratedCovariantTensorDerivative (metricDifferenceTensor g₀ h) j 0 v| ≤
          epsilon * ∏ i, ‖v i‖) ∧
      (∀ u v : TangentSpace (𝓡 3) (0 : EuclideanSpace ℝ (Fin 3)),
        LeviCivitaData.IsOrthonormalPair g₀ 0 u v → D₀.sectionalCurvature 0 u v = 1) := by
  obtain ⟨e, g₀, h, D₀, Dh, U, hU, h0, hUse, hep, he, hei, hinv, hg₀, hh, hzero, hΓ⟩ :=
    N.exists_normalCoordinateMetrics p
  have hg₀' : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
      g₀.inner y v w = N.model_metric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w) := by
    intro y hy v w
    exact congrArg (fun A => A v w) (hg₀ y hy)
  have hh' : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
      h.inner y v w = N.normalizedMetric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w) := by
    intro y hy v w
    exact congrArg (fun A => A v w) (hh y hy)
  refine ⟨e, g₀, h, D₀, Dh, U, hU, h0, hUse, hep, he, hei, hinv, hg₀', hh', hzero, hΓ, ?_, ?_⟩
  · have hnorm (v : EuclideanSpace ℝ (Fin 3)) :
        N.model_metric.tangentNorm (e 0) (mfderiv (𝓡 3) (𝓡 3) e 0 v) = ‖v‖ := by
      unfold RiemannianMetric.tangentNorm
      rw [← hg₀' 0 h0]
      change Real.sqrt (g₀.euclideanCoefficients 0 v v) = ‖v‖
      rw [hzero]
      exact (norm_eq_sqrt_re_inner (𝕜 := ℝ) v).symm
    intro j hj v
    have hpull := D₀.iteratedCovariantTensorDerivative_eq_pullback N.model_connection hU
      (he.mono hUse) hinv hg₀' (metricDifferenceTensor_isSmooth g₀ h) N.metricError_isSmooth
      (fun y hy w => by
        change h.inner y (w 0) (w 1) - g₀.inner y (w 0) (w 1) =
          N.normalizedMetric.inner (e y) (mfderiv (𝓡 3) (𝓡 3) e y (w 0))
            (mfderiv (𝓡 3) (𝓡 3) e y (w 1)) -
          N.model_metric.inner (e y) (mfderiv (𝓡 3) (𝓡 3) e y (w 0))
            (mfderiv (𝓡 3) (𝓡 3) e y (w 1))
        rw [hh' y hy, hg₀' y hy]) j h0 v
    rw [hpull]
    have hbound := N.covariantTwoJet_evaluation_le hepsilon j hj (e 0)
      (fun i => mfderiv (𝓡 3) (𝓡 3) e 0 (v i))
    simpa only [hnorm] using hbound
  · intro u v hpair
    rw [D₀.sectionalCurvature_eq_of_local_isometry N.model_connection hU
      (he.mono hUse) hg₀' h0]
    apply N.model_curvature_one
    simpa only [LeviCivitaData.IsOrthonormalPair, hg₀' 0 h0] using hpair

end PoincareConjecture.SingularRoundComponent
