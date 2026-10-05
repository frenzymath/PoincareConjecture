import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.LimitFiniteChartBounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.RelativeBilinearComparison

/-!
# Relative metric comparison on one compact chart region

Actual zeroth-jet convergence and a fixed positive limit ellipticity
constant give one relative quadratic comparison tail. Source:
Morgan--Tian Theorem 5.6, pp. 85-87; M28 derivation 118.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.RegularPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}

/-- The same retained source coefficients are uniformly comparable to
the actual limit coefficients on every fixed compact chart set. Source:
Theorem 5.6, pp. 85-87; M28 derivation 118. -/
theorem eventually_chart_relative_inner_bounds (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (K : Set (EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ (extChartAt (𝓡 n) q).target →
      ∀ tau : ℝ, 0 < tau → ∀ᶠ k in atTop, ∀ x ∈ K,
        ∀ v : EuclideanSpace ℝ (Fin n),
          (1 + tau)⁻¹ * G.limitMetric.pullbackCoefficients
            (extChartAt (𝓡 n) q).symm x v v ≤
            (g (G.subsequence k)).pullbackCoefficients
              (G.embedding k ∘ (extChartAt (𝓡 n) q).symm) x v v ∧
          (g (G.subsequence k)).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 n) q).symm) x v v ≤
            (1 + tau) * G.limitMetric.pullbackCoefficients
              (extChartAt (𝓡 n) q).symm x v v := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K hK htarget tau htau
  obtain ⟨a, _, _, ha, _, _, hbound⟩ :=
    G.exists_limit_finite_chart_bounds (fun _ : Unit => q) (fun _ => K)
      (fun _ => hK) (fun _ => htarget) 0
  have herror : 0 < (tau / (1 + tau)) * a := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_chart_coefficients q K hK htarget) _ herror] with k hk
  intro x hx v
  apply ContinuousLinearMap.relative_quadratic_bounds_of_norm_sub_le _ _ ha htau
    (fun w => ((hbound () x hx).1 w).1) _ v
  simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le

end PoincareMT.M28.RegularPointedMetricConvergence
