import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.ParametricIntegral

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_integral_of_kernel_derivative_bounds
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L : ℝ} (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    {U : Set E} (hU : IsOpen U) {k : E → M → ℝ}
    (hk : ∀ y, ContDiffOn ℝ ∞ (fun z ↦ k z y) U)
    (hmeas : ∀ m z, z ∈ U → AEStronglyMeasurable
      (fun y ↦ iteratedFDeriv ℝ m (fun w ↦ k w y) z) g.volumeMeasure)
    (hbound : ∀ z ∈ U, ∀ m : ℕ, ∃ V ∈ 𝓝 z, ∃ C : ℝ, ∃ x : M, ∃ t : ℝ,
      0 < t ∧ ∀ y w, w ∈ V ∩ U →
        ‖iteratedFDeriv ℝ m (fun p ↦ k p y) w‖ ≤ C * H.kernel x y t) :
    ContDiffOn ℝ ∞ (fun z ↦ ∫ y, f y * k z y ∂g.volumeMeasure) U ∧
      ∀ m z, z ∈ U →
        iteratedFDeriv ℝ m (fun w ↦ ∫ y, f y * k w y ∂g.volumeMeasure) z =
          ∫ y, f y • iteratedFDeriv ℝ m (fun w ↦ k w y) z ∂g.volumeMeasure := by
  have hderiv (m : ℕ) (z : E) (hz : z ∈ U) (y : M) :
      iteratedFDeriv ℝ m (fun w ↦ f y * k w y) z =
        f y • iteratedFDeriv ℝ m (fun w ↦ k w y) z := by
    exact iteratedFDeriv_const_smul_apply (a := f y)
      (((hk y).contDiffAt (hU.mem_nhds hz)).of_le (by
        exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)))
  have h := Poincare.Analysis.Heat.contDiffOn_integral_of_locally_dominated_iteratedFDeriv
    (μ := g.volumeMeasure) (f := fun z y ↦ f y * k z y) hU
    (ae_of_all _ (fun y ↦ (hk y).const_smul (f y))) ?_ ?_
  · refine ⟨h.1, fun m z hz ↦ (h.2 m z hz).trans ?_⟩
    apply integral_congr_ae
    exact ae_of_all _ (hderiv m z hz)
  · intro m z hz
    simp_rw [hderiv m z hz]
    exact hf.aestronglyMeasurable.smul (hmeas m z hz)
  · intro z hz m
    obtain ⟨V, hV, C, x, t, ht, hb⟩ := hbound z hz m
    refine ⟨V ∩ U, inter_mem hV (hU.mem_nhds hz),
      fun y ↦ C * |f y * H.kernel x y t|,
      (H.integrable_weighted_of_distance_lipschitz hf hLip x ht).norm.const_mul C, ?_⟩
    filter_upwards [] with y
    intro w hw
    rw [hderiv m w hw.2, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_pos (H.positive x y t ht)]
    simpa only [mul_left_comm] using
      mul_le_mul_of_nonneg_left (hb y w hw) (abs_nonneg (f y))

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
