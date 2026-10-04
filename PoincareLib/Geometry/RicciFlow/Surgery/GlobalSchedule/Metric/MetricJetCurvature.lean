import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Metric.MetricChartGerms
import PoincareLib.Geometry.Riemannian.Curvature.EuclideanNorm

/-!
# Curvature convergence at moving chart points

Realize each translated metric germ at zero, apply the fixed-point scalar
jet theorem, and identify its actual curvature norm with the original one.
The limiting metric is positive; no connection on that limiting manifold
needs to be supplied, since the local realization constructs its connection.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M51

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Scalar jets through order two at moving chart points give a finite
nonnegative limit for the actual curvature norms. -/
theorem curvatureNorm_limit_of_chart_jets
    {α : Type*} {l : Filter α} (g : α → RiemannianMetric 3 M)
    (D : ∀ i, LeviCivitaData (g i)) (g₀ : RiemannianMetric 3 M) (q : M)
    (z : α → EuclideanSpace ℝ (Fin 3))
    (hz : ∀ i, z i ∈ (extChartAt (𝓡 3) q).target)
    (p : EuclideanSpace ℝ (Fin 3)) (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hjets : ∀ k : ℕ, k ≤ 2 → ∀ a b : Fin 3,
      Tendsto (fun i => iteratedFDeriv ℝ k (singularMetricCoefficient (g i) q a b) (z i)) l
        (𝓝 (iteratedFDeriv ℝ k (singularMetricCoefficient g₀ q a b) p))) :
    ∃ L : ℝ, 0 ≤ L ∧
      Tendsto (fun i => (D i).curvatureTensorNorm ((extChartAt (𝓡 3) q).symm (z i))) l
        (𝓝 L) := by
  classical
  choose G DG hnorm hjet using fun i => exists_shiftedChartMetric (g i) q (z i) (hz i)
  obtain ⟨G₀, DG₀, _, hjet₀⟩ := exists_shiftedChartMetric g₀ q p hp
  refine ⟨DG₀.curvatureTensorNorm 0, Real.sqrt_nonneg _, ?_⟩
  have hconv := LeviCivitaData.tendsto_curvatureTensorNorm_of_scalar_metric_jets (l := l) DG DG₀ 0
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (fun k hk a b => ?_)
  · simpa only [funext (fun i => hnorm i (D i))] using hconv
  · change Tendsto (fun i => iteratedFDeriv ℝ k (fun y => (G i).inner y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0) l
      (𝓝 (iteratedFDeriv ℝ k (fun y => G₀.inner y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0))
    simpa only [hjet₀ k a b, funext (fun i => hjet i k a b)] using hjets k hk a b

end PoincareMT.M51
