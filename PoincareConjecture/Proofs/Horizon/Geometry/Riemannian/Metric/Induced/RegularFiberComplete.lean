import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen


set_option autoImplicit false
open Set TopologicalSpace Function Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff
namespace PoincareConjecture.RiemannianMetric

theorem metricComplete_openRegularFiberMetric_of_fullFiber
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U : Opens M) (hreg : ∀ x ∈ U,
      Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
    (c : Fin k → ℝ) (g : RiemannianMetric (m+k) M)
    (hc : MetricComplete g) (hfull : f ⁻¹' {c} ⊆ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    MetricComplete (openRegularFiberMetric hf U hreg c g) := by
  apply metricComplete_openRegularFiberMetric hf U hreg c g hc
  rw [inter_eq_right.mpr hfull]
  exact isClosed_singleton.preimage hf.continuous
end PoincareConjecture.RiemannianMetric
