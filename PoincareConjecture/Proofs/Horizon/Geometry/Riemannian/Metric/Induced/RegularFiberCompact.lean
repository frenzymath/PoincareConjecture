import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset


open Set
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff

theorem PoincareConjecture.RiemannianMetric.isCompact_openFiber_preimage_closedBall
    {n k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ} (hf : Continuous f) (U : TopologicalSpace.Opens M)
    (c : Fin k → ℝ) (p : M) (r : ℝ)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal r → y ∈ U) :
    IsCompact {z : openFiber f U c | g.edist p (openFiberIncl f U c z) ≤ ENNReal.ofReal r} := by
  apply (isEmbedding_openFiberIncl f U c).isCompact_iff.mpr
  have he : openFiberIncl f U c ''
      {z : openFiber f U c | g.edist p (openFiberIncl f U c z) ≤ ENNReal.ofReal r} =
      {y | g.edist p y ≤ ENNReal.ofReal r} ∩ f ⁻¹' {c} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.2⟩
    · rintro ⟨hy, hfy⟩
      exact ⟨⟨⟨y, hball y hy⟩, hfy⟩, hy, rfl⟩
  rw [he]
  exact (g.isCompact_closedBall_of_metricComplete hc p r).inter_right
    (isClosed_singleton.preimage hf)
