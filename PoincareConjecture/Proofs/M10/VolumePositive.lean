import PoincareConjecture.Proofs.M10.CalibratedPositive
import PoincareConjecture.Proofs.M10.VolumeTransport

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem reducedVolume_pos
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax) :
    0 < reducedVolume F T p τ := by
  have hi := reducedVolumeDensity_integrable hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax
  have hs : Function.support (reducedVolumeDensity F T p τ) = univ := by
    ext q
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (reducedVolumeDensity_pos hτ).ne'
  apply (integral_pos_iff_support_of_nonneg (fun _ ↦ reducedVolumeDensity_nonneg) hi).mpr
  rw [hs]
  exact calibratedMetricVolume_univ_pos _ p

end PoincareConjecture.M10
