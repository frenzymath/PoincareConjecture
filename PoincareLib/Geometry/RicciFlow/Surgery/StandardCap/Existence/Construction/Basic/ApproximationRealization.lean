import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.ApproximationEvolution
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometry

/-!
# Actual local metrics realizing the approximation coefficients

Each authorized chart germ is realized by a global Euclidean metric
with a genuine compatible connection. Its curvature norm at the base
point is the compact double's norm, by local isometry. These witnesses
allow passage of the full curvature bound to the limit in Theorem 12.5,
p. 297, without asserting global positivity of a truncated chart.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34.CompactCapApproximation

open SpacetimeBounds

variable {g0 : StandardInitialMetric} (A : CompactCapApproximation g0)

/-- A chart's actual coefficients are spatially smooth wherever its
differential is defined, at every total time (Theorem 12.5, p. 297). -/
theorem contDiffOn_coefficients_slice (k : ℕ) (t : ℝ) :
    ContDiffOn ℝ ∞ (A.coefficients k t) (compactCapSource g0 k) := by
  intro x hx
  exact (((A.flow k).metric t).contDiffAt_pullbackCoefficients
    ((compactCapChart_contMDiffOn g0 k).contMDiffAt
      ((compactCapSource_isOpen g0 k).mem_nhds hx))).contDiffWithinAt

/-- At each authorized point a global Euclidean metric realizes the
two-jet and retains the compact approximation's full curvature bound
(Theorem 12.5, p. 297). -/
theorem exists_metric_twoJet_realization (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time)
    {x : StandardCapSpace} (hx : x ∈ compactCapSource g0 k) :
    ∃ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g),
      metricTwoJet g.euclideanCoefficients x = metricTwoJet (A.coefficients k t) x ∧
        D.curvatureTensorNorm x ≤ A.curvature_bound 0 := by
  obtain ⟨g, D, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    (compactCapSource_isOpen g0 k) hx (A.coefficients k t)
    (A.contDiffOn_coefficients_slice k t)
    (fun _ _ _ _ => ((A.flow k).metric t).symm _ _ _) (fun y hy v hv => by
      apply ((A.flow k).metric t).pos
      intro hz
      apply hv
      apply (compactCapChart_mfderiv_isInvertible g0 k hy).injective
      rw [map_zero]
      convert! hz using 1)
  refine ⟨g, D, ?_, ?_⟩
  · apply metricTwoJet_congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  · have hnorm := D.curvatureTensorNorm_eq_of_local_isometry ((A.flow k).connection t)
      hV ((compactCapChart_contMDiffOn g0 k).mono hVU)
      (fun y hy u v => congrArg (fun B => B u v) (heq y hy)) hxV
    rw [hnorm]
    exact A.full_curvature_le k ht _

end PoincareMT.M34.CompactCapApproximation
