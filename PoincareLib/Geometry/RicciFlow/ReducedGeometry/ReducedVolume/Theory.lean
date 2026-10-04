import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Theory
import Mathlib.Topology.Algebra.Support

/-!
# Reduced-volume monotonicity

The complete ordinary-flow output includes the measure-theoretic regularity
needed by Chapter 7, both weak reduced-length inequalities, the minimum bound,
and the global and open-domain reduced-volume conclusions. The equality case
asserts one Euclidean identification for the entire closed time interval.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- The complete reduced-volume output for a complete ordinary Ricci flow. -/
structure ReducedVolumeTheory {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) where
  measure_regularity : ∀ p : M, Nonempty (ReducedLengthMeasureData F T τmax p)
  weak_inequalities : ∀ p : M, ∀ τ : ℝ, 0 < τ → τ < τmax →
    ∀ φ : M → ℝ, ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ φ → HasCompactSupport φ →
      (∀ q : M, 0 ≤ φ q) →
      MeasureTheory.Integrable (reducedLengthFirstWeakIntegrand F T p τ φ)
          (calibratedMetricVolume (F.metric (T - τ))) ∧
      MeasureTheory.Integrable (reducedLengthSecondWeakIntegrand F T p τ φ)
          (calibratedMetricVolume (F.metric (T - τ))) ∧
      0 ≤ ∫ q, reducedLengthFirstWeakIntegrand F T p τ φ q
        ∂calibratedMetricVolume (F.metric (T - τ)) ∧
      (∫ q, reducedLengthSecondWeakIntegrand F T p τ φ q
        ∂calibratedMetricVolume (F.metric (T - τ))) ≤ 0
  minimum_bound : ∀ p : M, ∀ τ : ℝ, 0 < τ → τ < τmax →
    ∃ q : M, (∀ q' : M, reducedLength F T p q τ ≤ reducedLength F T p q' τ) ∧
      reducedLength F T p q τ ≤ (n : ℝ) / 2
  density_integrable : ∀ p : M, ∀ τ : ℝ, 0 < τ → τ < τmax →
    MeasureTheory.Integrable (reducedVolumeDensity F T p τ)
      (calibratedMetricVolume (F.metric (T - τ)))
  volume_bounds : ∀ p : M, ∀ τ : ℝ, 0 < τ → τ < τmax →
    0 < reducedVolume F T p τ ∧ reducedVolume F T p τ ≤ euclideanReducedVolume n
  monotone : ∀ p : M, AntitoneOn (reducedVolume F T p) (Set.Ioo 0 τmax)
  zero_time_limit : ∀ p : M,
    Filter.Tendsto (reducedVolume F T p) (𝓝[>] (0 : ℝ)) (𝓝 (euclideanReducedVolume n))
  open_domain_monotone : ∀ p : M, ∀ A : Set (M × ℝ),
    IsBackwardLStarShaped F T τmax p A →
    AntitoneOn (fun τ ↦ reducedVolumeOn F T p τ {q | (q, τ) ∈ A}) (Set.Ioo 0 τmax)
  euclidean_rigidity : ∀ p : M, ∀ τ : ℝ, 0 < τ → τ < τmax →
    reducedVolume F T p τ = euclideanReducedVolume n →
    IsStaticEuclideanFlowOn F (Set.Icc (T - τ) T)

end PoincareMT
