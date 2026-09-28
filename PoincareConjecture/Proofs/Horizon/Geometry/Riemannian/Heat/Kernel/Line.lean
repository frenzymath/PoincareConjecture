import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineArclength
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineCoordinates

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Heat

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [PreconnectedSpace M] [NoncompactSpace M]

theorem exists_conservativeHeatKernelData_dim_one
    (g : RiemannianMetric 1 M) (hc : MetricComplete g) (D : LeviCivitaData g) :
    Nonempty (ConservativeHeatKernelData g) := by
  obtain ⟨e, he, hi, hmetric⟩ := g.exists_metric_line_coordinate hc
  exact D.exists_conservativeHeatKernelData_of_metric_line_coordinate g e he
    (hi.of_le (by simp)) hmetric

theorem exists_smooth_conservativeHeatKernel_dim_one
    (g : RiemannianMetric 1 M) (hc : MetricComplete g) (D : LeviCivitaData g) :
    ∃ H : M → M → ℝ → ℝ,
      (∀ x y t, 0 < t → 0 < H x y t) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod (𝓡 1)).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : (ℝ × M) × M => H p.1.2 p.2 p.1.1) ((Ioi 0 ×ˢ univ) ×ˢ univ) ∧
      (∀ x y t, 0 < t → HasDerivAt (fun s => H x y s)
        (D.laplacian (fun z => H z y t) x) t) ∧
      (∀ x t, 0 < t → ∫ y, H x y t ∂g.volumeMeasure = 1) ∧
      (∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ → ∀ x,
        Tendsto (fun t => ∫ y, H x y t * φ y ∂g.volumeMeasure)
          (𝓝[>] 0) (𝓝 (φ x))) ∧
      (∀ x t, 0 < t → Integrable
        (fun y => (g.edist x y).toReal * H x y t) g.volumeMeasure) ∧
      (∀ x t, 0 < t → t ≤ 1 →
        ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure ≤ Real.sqrt 2) ∧
      Tendsto (fun t => ⨆ x,
        ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨e, he, hi, hmetric⟩ := g.exists_metric_line_coordinate hc
  have hed := g.edist_eq_of_metric_line_coordinate e (he.of_le (by simp))
    (hi.of_le (by simp)) hmetric
  refine ⟨fun x y t => realHeatKernel t (e y - e x), ?_,
    LeviCivitaData.contMDiffOn_realHeatKernel_coordinate he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y t ht => transported_realHeatKernel_pos g e hed ht x y
  · exact fun x y t ht => D.hasDerivAt_realHeatKernel_of_metric_coordinate he hmetric y ht x
  · exact fun x t ht => transported_realHeatKernel_mass_one g e hed ht x
  · exact fun φ hφ hφc x => tendsto_transported_realHeatKernel_initial g e hed hφ hφc x
  · exact fun x t ht => transported_realHeatKernel_first_moment_integrable g e hed ht x
  · exact fun x t ht ht1 => transported_realHeatKernel_first_moment_bound g e hed ht ht1 x
  · exact tendsto_transported_realHeatKernel_first_moment g e hed

end PoincareConjecture.RiemannianMetric
