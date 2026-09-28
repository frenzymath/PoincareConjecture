import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.Evolution
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricFlowApproximation

open SpacetimeBounds

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)] (A : MetricFlowApproximation ginit Mfamily)

theorem contDiffOn_coefficients_slice (k : ℕ) (t : ℝ) :
    ContDiffOn ℝ ∞ (A.coefficients k t) (A.source k) := by
  intro x hx
  exact (((A.flow k).metric t).contDiffAt_pullbackCoefficients
    ((A.chart_smooth k).contMDiffAt
      ((A.source_isOpen k).mem_nhds hx))).contDiffWithinAt

theorem exists_metric_twoJet_realization (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time)
    {x : StandardCapSpace} (hx : x ∈ A.source k) :
    ∃ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g),
      metricTwoJet g.euclideanCoefficients x = metricTwoJet (A.coefficients k t) x ∧
        D.curvatureTensorNorm x ≤ A.curvature_bound 0 := by
  obtain ⟨g, D, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    (A.source_isOpen k) hx (A.coefficients k t)
    (A.contDiffOn_coefficients_slice k t)
    (fun _ _ _ _ => ((A.flow k).metric t).symm _ _ _) (fun y hy v hv => by
      apply ((A.flow k).metric t).pos
      intro hz
      apply hv
      apply (A.chart_invertible k _ hy).injective
      rw [map_zero]
      convert! hz using 1)
  refine ⟨g, D, ?_, ?_⟩
  · apply metricTwoJet_congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  · have hnorm := D.curvatureTensorNorm_eq_of_local_isometry ((A.flow k).connection t)
      hV ((A.chart_smooth k).mono hVU)
      (fun y hy u v => congrArg (fun B => B u v) (heq y hy)) hxV
    rw [hnorm]
    exact A.full_curvature_le k ht _

end PoincareConjecture.M34.MetricFlowApproximation
