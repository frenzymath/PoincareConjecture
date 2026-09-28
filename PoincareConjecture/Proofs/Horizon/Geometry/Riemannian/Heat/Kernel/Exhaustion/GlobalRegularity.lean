import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Regularity

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

theorem exists_jointlySmooth_dirichletExhaustionKernel
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] [PreconnectedSpace M]
    [NoncompactSpace M] {g : RiemannianMetric (n + 1) M}
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 (n + 1)) x),
      -k * g.inner x v v ≤ D.ricci x v v) :
    ∃ (Ω : ℕ → Set M) (S : ∀ q, Poincare.Manifold.SmoothDomain (n + 1) (Ω q)),
      Monotone Ω ∧ (⋃ q, Ω q) = univ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod (𝓡 (n + 1))).prod (𝓡 (n + 1)))
        𝓘(ℝ, ℝ) ∞
        (fun p : (ℝ × M) × M => dirichletExhaustionKernel
          (fun q => Dirichlet.heatKernelContinuousTime D (S q))
          p.1.1 p.1.2 p.2) ((Ioi 0 ×ˢ univ) ×ˢ univ) := by
  obtain ⟨Ω, S, hnest, hcover, _, hmono⟩ :=
    D.exists_canonical_dirichletHeatKernel_exhaustion
  have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hnest j)
  refine ⟨Ω, S, hΩmono, hcover, ?_⟩
  exact Dirichlet.contMDiffOn_dirichletExhaustionKernel D hc hk hRic S hΩmono hcover

end PoincareConjecture.LeviCivitaData
