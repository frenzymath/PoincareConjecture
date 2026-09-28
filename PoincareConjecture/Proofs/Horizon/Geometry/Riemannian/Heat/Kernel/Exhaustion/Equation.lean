import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.WeakEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.WeakToStrong

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

theorem hasDerivAt_dirichletExhaustionKernel_laplacian
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (x y : M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => dirichletExhaustionKernel (fun q => heatKernelContinuousTime D (S q)) r x y)
      (D.laplacian (fun z => dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) t z y) x) t := by
  have hs := contMDiffOn_dirichletExhaustionKernel D hc hk hRic S hΩmono hcover
  have hm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) ∞
      (fun p : ℝ × M => (p, y)) (Ioi 0 ×ˢ univ) :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn
  have hF := hs.comp hm (fun p hp => ⟨hp, mem_univ y⟩)
  exact D.hasDerivAt_of_smooth_weak_heatEquation hF ht
    (fun φ hφ hφc => hasDerivAt_integral_test_mul_dirichletExhaustionKernel
      D hc hk hRic S hΩmono hcover y hφ hφc ht) x

end PoincareConjecture.LeviCivitaData.Dirichlet
