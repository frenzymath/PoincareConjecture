import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RayComparison








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]



theorem laplacian_inverse_branch_le_of_ricci
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ U)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {b t k : ℝ} (hb : 0 < b) (ht : t ∈ Ioo 0 b) (hk : 0 ≤ k)
    (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U)
    (hi : ∀ s ∈ Icc 0 b,
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ)))
    (hRic : ∀ s ∈ Ioo 0 b, ∀ v : TangentSpace (𝓡 (m + 1)) (e (s • θ)),
      -(m : ℝ) * k ^ 2 * g.inner (e (s • θ)) v v ≤ D.ricci (e (s • θ)) v v)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1))) M)
    (heB : EqOn e B B.source)
    (hB : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B.symm B.target)
    (htB : t • θ ∈ B.source)
    (hgauss : ∀ᶠ y in 𝓝 (t • θ), ∀ v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e y) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y v) = inner ℝ y v) :
    D.laplacian (fun y => ‖B.symm y‖) (e (t • θ)) ≤ (m : ℝ) / t + (m : ℝ) * k := by
  have ht' : t ∈ Icc 0 b := ⟨ht.1.le, ht.2.le⟩
  have hρ := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (hU.mem_nhds (hsub t ht'))) (hi t ht')
  exact g.laplacian_inverse_branch_le_of_polar_comparison D hm θ hθ ht hk
    (hρ.1.differentiableAt (by simp)) hρ.2
    (fun u hu v hv huv => g.polarDensity_cross_le_on_regular_ray D hm hU h0 he hgeo
      hmetric θ hθ hb (sq_nonneg k) hsub hi hRic hu hv huv)
    B heB hB hBi htB hgauss

end PoincareConjecture.RiemannianMetric
