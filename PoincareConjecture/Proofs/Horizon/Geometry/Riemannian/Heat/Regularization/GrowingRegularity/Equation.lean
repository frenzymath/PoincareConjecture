import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.Approximation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.CompactEquation

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

open LeviCivitaData

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hasDerivAt_integral_test_mul_kernel_integral_of_exhaustion
    (H : ConservativeHeatKernelData g) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ x y t, H.kernel x y t = dirichletExhaustionKernel
      (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y)
    (O : M) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (D.gradient f x) ≤ 2)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => ∫ x, φ x * (∫ y, f y * H.kernel x y r ∂g.volumeMeasure) ∂g.volumeMeasure)
      (∫ x, (∫ y, f y * H.kernel x y t ∂g.volumeMeasure) * D.laplacian φ x
        ∂g.volumeMeasure) t := by
  obtain ⟨u, hu, huc, hub, _, hue⟩ :=
    D.exists_compact_distance_approximations hc O hf happrox hgrad
  have hLip : ∀ x y, |f y - f x| ≤ 2 * (g.edist x y).toReal := by
    intro x y
    rw [abs_sub_comm]
    exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hf.of_le (by simp)) (K := 2) (by norm_num)
      (fun z => (D.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z)) x y
  have hlim := H.tendstoLocallyUniformlyOn_integral_of_exhaustion D hc hk hRic
    S hΩmono hcover hkernel hf.continuous hLip (fun j => (hu j).continuous) hub
    (fun y => tendsto_const_nhds.congr' (by
      filter_upwards [hue y] with j hj
      exact hj.self_of_nhds.symm))
  apply D.hasDerivAt_integral_test_mul_of_exhaustion
    (Ω := fun _ : ℕ => (univ : Set M)) (fun _ => isOpen_univ)
    (fun _ _ _ => subset_rfl) (by
      apply Subset.antisymm (subset_univ _)
      intro x _
      exact mem_iUnion.mpr ⟨0, mem_univ x⟩)
    (F := fun j p => ∫ y, u j y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
    (U := fun p => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
    ?_ ?_ hlim hφ hφc ht
  · intro j
    simpa only [hkernel] using Dirichlet.contMDiffOn_dirichletExhaustionKernel_integral
      D hc hk hRic S hΩmono hcover (hu j) (huc j)
  · intro j r hr x _
    simpa only [hkernel] using
      Dirichlet.hasDerivAt_dirichletExhaustionKernel_integral_laplacian
        D hc hk hRic S hΩmono hcover (hu j) (huc j) hr x

theorem hasDerivAt_kernel_integral_of_exhaustion_of_contMDiff
    (H : ConservativeHeatKernelData g) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ x y t, H.kernel x y t = dirichletExhaustionKernel
      (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y)
    (O : M) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (D.gradient f x) ≤ 2)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
      (Ioi 0 ×ˢ univ)) {t : ℝ} (ht : 0 < t) (x : M) :
    HasDerivAt (fun r => ∫ y, f y * H.kernel x y r ∂g.volumeMeasure)
      (D.laplacian (fun z => ∫ y, f y * H.kernel z y t ∂g.volumeMeasure) x) t := by
  apply D.hasDerivAt_of_smooth_weak_heatEquation hF ht _ x
  intro φ hφ hφc
  exact H.hasDerivAt_integral_test_mul_kernel_integral_of_exhaustion
    D hc hk hRic S hΩmono hcover hkernel O hf happrox hgrad hφ hφc ht

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
