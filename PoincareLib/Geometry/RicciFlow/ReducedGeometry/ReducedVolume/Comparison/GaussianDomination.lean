import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.InitialTime.InitialWeightedLimit
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.RegularWeights
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.SourceGaussian

/-!
# The produced Gaussian majorant for actual regular rays

Ray antitonicity and the actual initial limit give the Gaussian estimate.
The measurable zero extension is therefore integrable on the fixed source
space, with its pointwise initial limit retained by initial coverage.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

/-- Initial coverage preserves the actual Gaussian ray limit under zero extension. -/
theorem regularWeightedJacobian_tendsto_initial
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun τ : ℝ ↦ regularWeightedJacobian G τ x) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2))) :=
  (weightedExponentialJacobian_tendsto_initial G hmax hT hwindow hcurvature x).congr'
    (regularWeightedJacobian_eventually_eq G x).symm

variable [ConnectedSpace M]

/-- The actual initial limit and ray monotonicity bound every regular weight by the Gaussian. -/
theorem weightedExponentialJacobian_le_sourceGaussian
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain) :
    weightedExponentialJacobian G τ x ≤ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2) := by
  obtain ⟨hτ, _, _, _⟩ := hreg.1
  apply ge_of_tendsto (weightedExponentialJacobian_tendsto_initial G hmax hT hwindow hcurvature x)
  filter_upwards [Ioo_mem_nhdsGT hτ] with s hs
  exact weightedExponentialJacobian_antitoneOn hwindow hL hDifferential G x
    (G.backward_nesting _ τ hreg s hs.1 hs.2.le) hreg hs.2.le

/-- The zero extension has the same Gaussian majorant on the whole source space. -/
theorem regularWeightedJacobian_le_sourceGaussian
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    regularWeightedJacobian G τ x ≤ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2) := by
  classical
  by_cases hx : x ∈ (exponentialSliceChart G τ).source
  · rw [regularWeightedJacobian, indicator_of_mem hx]
    exact weightedExponentialJacobian_le_sourceGaussian hL hDifferential G hmax hT hwindow
      hcurvature x (by rwa [exponentialSliceChart_source] at hx)
  · simpa only [regularWeightedJacobian, indicator_of_notMem hx] using
      (sourceGaussian_pos n x).le

/-- The produced Gaussian estimate proves integrability of the actual source weight. -/
theorem regularWeightedJacobian_integrable
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax) :
    Integrable (regularWeightedJacobian G τ) := by
  apply (sourceGaussian_integrable n).mono'
    (regularWeightedJacobian_measurable G hτ hτmax).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (regularWeightedJacobian_nonneg G hτ x)]
  exact regularWeightedJacobian_le_sourceGaussian hL hDifferential G hmax hT hwindow hcurvature τ x

end PoincareMT.ReducedVolume
