import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Continuity.FullSourceContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The actual weighted regular rays extended by zero

The canonical regular source is open and backward nested. Its weighted
Jacobian is continuous on the source, so extending by zero is measurable.
Initial coverage and pointwise monotonicity retain the exact source domain.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

/-- The actual weighted Jacobian on its canonical regular source, zero elsewhere. -/
noncomputable def regularWeightedJacobian (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (exponentialSliceChart G τ).source.indicator (weightedExponentialJacobian G τ) x

/-- Extending the actual weight by zero preserves nonnegativity. -/
theorem regularWeightedJacobian_nonneg (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ regularWeightedJacobian G τ x := by
  classical
  by_cases hx : x ∈ (exponentialSliceChart G τ).source
  · simpa only [regularWeightedJacobian, indicator_of_mem hx] using
      weightedExponentialJacobian_nonneg G hτ x
  · simp only [regularWeightedJacobian, indicator_of_notMem hx, le_refl]

/-- The actual action and Jacobian make the weight continuous on its regular source. -/
theorem weightedExponentialJacobian_continuousOn
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    ContinuousOn (weightedExponentialJacobian G τ) (exponentialSliceChart G τ).source :=
  (weightedExponentialJacobian_continuous G hτ hmax).continuousOn

/-- The zero extension is measurable without any assertion of continuity at the cut locus. -/
theorem regularWeightedJacobian_measurable
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Measurable (regularWeightedJacobian G τ) := by
  classical
  exact (weightedExponentialJacobian_continuousOn G hτ hmax).measurable_piecewise
    continuousOn_const (exponentialSliceChart G τ).open_source.measurableSet

/-- Each fixed vector belongs to the canonical regular source at all sufficiently small times. -/
theorem eventually_mem_exponentialSlice_source
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), x ∈ (exponentialSliceChart G τ).source := by
  obtain ⟨δ, hδ, _, hcover⟩ := G.bounded_initial_coverage ‖x‖ (norm_nonneg _)
  filter_upwards [Ioo_mem_nhdsGT hδ] with τ hτ
  rw [exponentialSliceChart_source]
  exact hcover (metricCoordinates (F.metric T) p x)
    (by rw [metricCoordinates_tangentNorm]) τ hτ.1 hτ.2

/-- Initial coverage makes the zero extension eventually equal to the actual smooth ray. -/
theorem regularWeightedJacobian_eventually_eq
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) :
    (fun τ ↦ regularWeightedJacobian G τ x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun τ ↦ weightedExponentialJacobian G τ x) := by
  filter_upwards [eventually_mem_exponentialSlice_source G x] with τ hτ
  exact indicator_of_mem hτ _

variable [ConnectedSpace M]

/-- Backward nesting and the actual ray derivative give monotonicity of the zero extension. -/
theorem regularWeightedJacobian_antitoneOn
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) :
    AntitoneOn (fun τ ↦ regularWeightedJacobian G τ x) (Ioo 0 τmax) := by
  classical
  intro a ha b hb hab
  by_cases hx : x ∈ (exponentialSliceChart G b).source
  · have hreg : (metricCoordinates (F.metric T) p x, b) ∈
        G.toLExponentialFamily.regularDomain := by
      rwa [exponentialSliceChart_source] at hx
    have hrega := G.backward_nesting _ b hreg a ha.1 hab
    have hxa : x ∈ (exponentialSliceChart G a).source := by
      rwa [exponentialSliceChart_source]
    simp only [regularWeightedJacobian, indicator_of_mem hx, indicator_of_mem hxa]
    exact weightedExponentialJacobian_antitoneOn hwindow hL hDifferential G x hrega hreg hab
  · simpa only [regularWeightedJacobian, indicator_of_notMem hx] using
      regularWeightedJacobian_nonneg G ha.1 x

end PoincareMT.ReducedVolume
