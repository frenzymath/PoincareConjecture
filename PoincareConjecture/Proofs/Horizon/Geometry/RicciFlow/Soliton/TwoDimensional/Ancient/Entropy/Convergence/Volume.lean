import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.UniformLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.TotalCurvature


set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SurfaceEntropy

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]


theorem eventually_volume_le_of_uniform_scalar
    {g : ℕ → RiemannianMetric 2 M} (D : ∀ k, LeviCivitaData (g k)) {c : ℝ}
    (hc : 0 < c)
    (hR : TendstoUniformly (fun k x => (D k).scalarCurvature x) (fun _ => c) atTop) :
    ∀ᶠ k in atTop, (g k).volumeMeasure.real univ ≤ 16 * Real.pi / c := by
  filter_upwards [Metric.tendstoUniformly_iff.mp hR (c / 2) (by positivity)] with k hk
  have hlo : ∀ x, c / 2 ≤ (D k).scalarCurvature x := by
    intro x
    have h := (abs_lt.mp (show |c - (D k).scalarCurvature x| < c / 2 from
      by simpa only [Real.dist_eq] using hk x)).2
    linarith
  have hi := (D k).continuous_scalarCurvature.integrable_of_hasCompactSupport
    (μ := (g k).volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have harea := integral_mono (integrable_const (c / 2)) hi hlo
  rw [integral_const, smul_eq_mul] at harea
  have htotal := (D k).integral_scalarCurvature_le_eight_pi
  apply (le_div_iff₀ hc).mpr
  nlinarith

end PoincareConjecture.SurfaceEntropy
