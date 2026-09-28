import PoincareConjecture.Proofs.M35.Thm12_28.FixedMetricSmoothness

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_chart_cancel
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n N) (f : M → N) (q : M) {y : M}
    (hy : y ∈ (extChartAt (𝓡 n) q).source)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f y)
    (v w : TangentSpace (𝓡 n) y) :
    g.pullbackCoefficients (f ∘ (extChartAt (𝓡 n) q).symm) (extChartAt (𝓡 n) q y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q) y v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q) y w) =
    g.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) := by
  let c := extChartAt (𝓡 n) q
  have hcy : c y ∈ c.target := c.map_source hy
  have hinv : c.symm (c y) = y := c.left_inv hy
  have hf' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (c.symm (c y)) := hinv.symm ▸ hf
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hcy)
  have hchartsource : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source := by
    rwa [← extChartAt_source (I := 𝓡 n)]
  have hcforward := contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hchartsource
  have heq : (f ∘ c.symm) ∘ c =ᶠ[𝓝 y] f := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓡 n) q).mem_nhds hy] with z hz
    exact congrArg f (c.left_inv hz)
  have hd : mfderiv (𝓡 n) (𝓡 n) ((f ∘ c.symm) ∘ c) y =
      mfderiv (𝓡 n) (𝓡 n) f y := heq.mfderiv_eq
  have hchain := mfderiv_comp y
    ((hf'.comp (c y) hc).mdifferentiableAt (by simp))
    (hcforward.mdifferentiableAt (by simp))
  have hv (u : TangentSpace (𝓡 n) y) := congrArg
    (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A u)
    (hchain.symm.trans hd)
  have hpoint := congrArg (fun z : N =>
    g.inner z (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w))
    (congrArg f hinv)
  exact (congrArg₂ (fun a b : EuclideanSpace ℝ (Fin n) => g.inner (f (c.symm (c y))) a b)
    (hv v) (hv w)).trans hpoint

theorem chartCoefficients_cancel
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (q : M) {y : M}
    (hy : y ∈ (extChartAt (𝓡 n) q).source) (v w : TangentSpace (𝓡 n) y) :
    g.pullbackCoefficients (extChartAt (𝓡 n) q).symm (extChartAt (𝓡 n) q y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q) y v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q) y w) = g.inner y v w := by
  have h := g.pullbackCoefficients_chart_cancel id q hy contMDiffAt_id v w
  simpa only [Function.id_comp, id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using h

end PoincareConjecture.RiemannianMetric
