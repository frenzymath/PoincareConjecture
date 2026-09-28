import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence














noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (g : RiemannianMetric n M) {γ : ℝ → M}



theorem abs_busemannApprox_le_base_distance
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {t : ℝ} (ht : 0 ≤ t) (x : M) :
    |g.busemannApprox γ t x| ≤ (g.edist (γ 0) x).toReal := by
  refine abs_le.mpr ⟨?_, g.busemannApprox_le_distance hγ t x⟩
  simpa only [busemannApprox, zero_sub] using g.busemannApprox_monotone hγ x ht

variable [MeasurableSpace M] [BorelSpace M]


theorem integrable_busemann_mul_compact_test
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {ψ : M → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => g.busemann γ x * ψ x) g.volumeMeasure :=
  ((g.continuous_busemann hγ).mul hψ).integrable_of_hasCompactSupport hc.mul_left



theorem tendsto_integral_busemannApprox_mul_compact_test
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {ψ : M → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun t : ℝ => ∫ x, g.busemannApprox γ t x * ψ x ∂g.volumeMeasure)
      atTop (𝓝 (∫ x, g.busemann γ x * ψ x ∂g.volumeMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => (g.edist (γ 0) x).toReal * ‖ψ x‖)
  · exact Eventually.of_forall fun t =>
      ((g.continuous_busemannApprox γ t).mul hψ).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (g.abs_busemannApprox_le_base_distance hγ ht x)
        (norm_nonneg _)
  · exact ((g.continuous_toReal_edist (γ 0)).mul hψ.norm).integrable_of_hasCompactSupport
      hc.norm.mul_left
  · exact Eventually.of_forall fun x => (g.tendsto_busemannApprox hγ x).mul_const (ψ x)


theorem tendsto_integral_busemannApprox_mul_laplacian
    (D : LeviCivitaData g)
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) :
    Tendsto (fun t : ℝ =>
      ∫ x, g.busemannApprox γ t x * D.laplacian φ x ∂g.volumeMeasure)
      atTop (𝓝 (∫ x, g.busemann γ x * D.laplacian φ x ∂g.volumeMeasure)) :=
  g.tendsto_integral_busemannApprox_mul_compact_test hγ (D.continuous_laplacian hφ)
    (hc.of_isClosed_subset (isClosed_tsupport _) (D.tsupport_laplacian_subset φ))

end PoincareConjecture.RiemannianMetric
