import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RiemannianMetric

open LeviCivitaData

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric (m + 1) M}



def canonicalConservativeHeatKernelData
    (D : LeviCivitaData g) (hm : 0 < m) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ) :
    ConservativeHeatKernelData g := by
  let F := fun j => Dirichlet.heatKernelContinuousTime D (S j)
  have hDom : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (F j) :=
    fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  have hmono := fun (t : ℝ) (ht : 0 < t) x y =>
    D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y
  have hk : 0 ≤ (m : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  have hRic' : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -((m : ℝ) * K) * g.inner x v v ≤ D.ricci x v v := by
    simpa only [neg_mul] using hRic
  have hbdd (t : ℝ) (ht : 0 < t) (x y : M) :
      BddAbove (range (fun j => F j t x y)) :=
    D.bddAbove_heatKernelContinuousTime_exhaustion (Nat.succ_pos _) hc hk hRic'
      S hΩmono hcover ht x y
  have hsmooth := Dirichlet.contMDiffOn_dirichletExhaustionKernel
    D hc hk hRic' S hΩmono hcover
  have hheat := Dirichlet.hasDerivAt_dirichletExhaustionKernel_laplacian
    D hc hk hRic' S hΩmono hcover
  let C := Classical.choose (exists_dirichletExhaustionKernel_first_moment_bound m K hm hK)
  have hC := (Classical.choose_spec
    (exists_dirichletExhaustionKernel_first_moment_bound m K hm hK)).1
  have hmoment := (Classical.choose_spec
    (exists_dirichletExhaustionKernel_first_moment_bound m K hm hK)).2
  have hmom := hmoment M g hc D hRic Ω S hΩmono hcover
  exact {
    connection := D
    kernel := fun x y t => dirichletExhaustionKernel F t x y
    positive := fun x y t ht => DirichletExhaustion.positive
      hDom hbdd hΩmono hcover ht x y
    smooth := fun x y t ht => by
      have hmap : ContMDiff (𝓡 (m + 1))
          ((𝓘(ℝ, ℝ).prod (𝓡 (m + 1))).prod (𝓡 (m + 1))) ∞
          (fun z : M => ((t, z), y)) :=
        (contMDiff_const.prodMk contMDiff_id).prodMk contMDiff_const
      exact (contMDiffOn_univ.mp (hsmooth.comp hmap.contMDiffOn
        (s := univ) (fun z _ => ⟨⟨ht, mem_univ z⟩, mem_univ y⟩))).contMDiffAt
    timeDifferentiable := fun x y t ht => (hheat x y ht).differentiableAt
    mass_one := fun x t ht => D.integral_dirichletExhaustionKernel_eq_one
      hm hc hK hRic S hΩmono hcover ht x
    initial := fun φ hφ hφc x => tendsto_integral_iSup_dirichletHeatKernel_initial
      hDom hcover hmono hbdd hφ hφc x
    heat_equation := fun x y t ht => (hheat x y ht).deriv
    first_moment_integrable := fun x t ht =>
      D.integrable_dirichletExhaustionKernel_distance_all_time
        hm hc hK hRic S hΩmono hcover ht x
    first_moment_bound := ⟨C, hC, fun x t ht ht1 => (hmom.1 x t ht ht1).2⟩
    first_moment_tendsto_zero := hmom.2 }

@[simp] theorem canonicalConservativeHeatKernelData_connection
    (D : LeviCivitaData g) (hm : 0 < m) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ) :
    (canonicalConservativeHeatKernelData D hm hc hK hRic S hΩmono hcover).connection = D := rfl

@[simp] theorem canonicalConservativeHeatKernelData_kernel
    (D : LeviCivitaData g) (hm : 0 < m) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ) (x y : M) (t : ℝ) :
    (canonicalConservativeHeatKernelData D hm hc hK hRic S hΩmono hcover).kernel x y t =
      dirichletExhaustionKernel (fun j => Dirichlet.heatKernelContinuousTime D (S j))
        t x y := rfl



theorem exists_canonical_kernel_integral_displacement_bound
    (m : ℕ) (K : ℝ) (hm : 0 < m) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
        (g : RiemannianMetric (m + 1) M) (hc : MetricComplete g)
        (D : LeviCivitaData g)
        (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
          -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v)
        (Ω : ℕ → Set M) (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
        (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
        (f : M → ℝ), ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ f →
        (∀ x, g.tangentNorm x (D.gradient f x) ≤ 2) →
        let H := canonicalConservativeHeatKernelData D hm hc hK hRic S hΩmono hcover
        (∀ t, 0 < t → ∀ x,
          Integrable (fun y => f y * H.kernel x y t) g.volumeMeasure) ∧
        TendstoUniformly (fun t x => ∫ y, f y * H.kernel x y t ∂g.volumeMeasure)
          f (𝓝[>] 0) ∧
        (∀ t ∈ Ioc 0 1, ∀ x,
          |(∫ y, f y * H.kernel x y t ∂g.volumeMeasure) - f x| ≤ C) := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_dirichletExhaustionKernel_first_moment_bound m K hm hK
  refine ⟨2 * C, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ g hc D hRic Ω S hΩmono hcover f hf hgrad
  let H := canonicalConservativeHeatKernelData D hm hc hK hRic S hΩmono hcover
  have hLip : ∀ x y, |f y - f x| ≤ 2 * (g.edist x y).toReal := by
    intro x y
    rw [abs_sub_comm]
    exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hf.of_le (by simp)) (K := 2) (by norm_num)
      (fun z => (D.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z)) x y
  refine ⟨fun t ht x => H.integrable_weighted_of_distance_lipschitz hf.continuous hLip x ht,
    H.tendstoUniformly_kernel_integral hf.continuous (by norm_num) hLip, ?_⟩
  intro t ht x
  exact H.regularization_displacement_bound hf.continuous (by norm_num) hLip
    (fun z s hs hs1 => (hmoment M g hc D hRic Ω S hΩmono hcover).1 z s hs hs1 |>.2)
    ht.1 ht.2

end PoincareConjecture.RiemannianMetric
