import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47




theorem limitNoncollapse_capture_ball
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [T3Space M] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : OpenPartialHomeomorph M N) (p : M)
    {R r C : ℝ} (hR : 0 < R) (hC : 0 < C) (hCr : C * r < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hsource : closure (g.ball p R) ⊆ e.source)
    (hinv : ∀ y ∈ e.target, ContMDiffAt (𝓡 3) (𝓡 3) 1 e.symm y)
    (hbound : ∀ y ∈ e '' closure (g.ball p R),
      ∀ v : TangentSpace (𝓡 3) y,
        g.tangentNorm (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v) ≤
          C * h.tangentNorm y v) :
    h.ball (e p) r ⊆ e '' g.ball p (C * r) := by
  exact RiemannianMetric.ball_subset_image_ball_of_inverse_tangentNorm_le
    g h e p hR hC hCr hcompact hsource hinv hbound



theorem limitNoncollapse_image_volume_le
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [T3Space M] [T2Space N] [T3Space N] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : OpenPartialHomeomorph M N) {V : Set M} (hV : IsOpen V)
    (hVe : V ⊆ e.source)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ V, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) ≤
        C * g.tangentNorm z v)
    {s : Set M} (hs : MeasurableSet s) (hsV : s ⊆ V) :
    h.volumeMeasure (e '' s) ≤ ENNReal.ofReal C ^ 3 * g.volumeMeasure s := by
  exact RiemannianMetric.volumeMeasure_image_le_of_tangentNorm_le
    g h e hV hVe he hC hbound hs hsV

end PoincareConjecture.M47
