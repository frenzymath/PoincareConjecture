import PoincareConjecture.Proofs.M10.VolumeTransport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem reducedVolume_le_euclidean
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax) :
    reducedVolume F T p τ ≤ euclideanReducedVolume n := by
  rw [reducedVolume_eq_integral_regularWeight hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax, ← integral_sourceGaussian n]
  exact integral_mono
    (regularWeightedJacobian_integrable hL hDifferential G hmax hT hwindow hcurvature hτ hτmax)
    (sourceGaussian_integrable n)
    (regularWeightedJacobian_le_sourceGaussian hL hDifferential G hmax hT hwindow hcurvature τ)

theorem reducedVolume_antitoneOn
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    AntitoneOn (reducedVolume F T p) (Ioo 0 τmax) := by
  intro a ha b hb hab
  rw [reducedVolume_eq_integral_regularWeight hL hDifferential G hmax hT hwindow
      hcurvature hb.1 hb.2,
    reducedVolume_eq_integral_regularWeight hL hDifferential G hmax hT hwindow
      hcurvature ha.1 ha.2]
  exact integral_mono
    (regularWeightedJacobian_integrable hL hDifferential G hmax hT hwindow hcurvature hb.1 hb.2)
    (regularWeightedJacobian_integrable hL hDifferential G hmax hT hwindow hcurvature ha.1 ha.2)
    (fun x ↦ regularWeightedJacobian_antitoneOn hwindow hL hDifferential G x ha hb hab)

theorem reducedVolume_tendsto_zero
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    Tendsto (reducedVolume F T p) (𝓝[>] (0 : ℝ)) (𝓝 (euclideanReducedVolume n)) := by
  have hsmall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioo 0 τmax := Ioo_mem_nhdsGT hmax
  have hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (regularWeightedJacobian G τ) volume := by
    filter_upwards [hsmall] with τ hτ
    exact (regularWeightedJacobian_measurable G hτ.1 hτ.2).aestronglyMeasurable
  have hbound : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      ‖regularWeightedJacobian G τ x‖ ≤ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2) := by
    filter_upwards [hsmall] with τ hτ
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (regularWeightedJacobian_nonneg G hτ.1 x)]
    exact regularWeightedJacobian_le_sourceGaussian hL hDifferential G hmax hT hwindow
      hcurvature τ x
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2))
    hmeas hbound (sourceGaussian_integrable n)
    (ae_of_all _ (regularWeightedJacobian_tendsto_initial G hmax hT hwindow hcurvature))
  rw [integral_sourceGaussian] at hlim
  apply hlim.congr'
  filter_upwards [hsmall] with τ hτ
  exact (reducedVolume_eq_integral_regularWeight hL hDifferential G hmax hT hwindow
    hcurvature hτ.1 hτ.2).symm

end PoincareConjecture.M10
