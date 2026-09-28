import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GradientLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.VolumeGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.CompactEquation

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem compact_kernel_evolution_gradient_bound
    (H : ConservativeHeatKernelData g) (hn : 1 ≤ n) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K) (O : M)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u) (huc : HasCompactSupport u)
    {B : ℝ} (hB : 0 ≤ B)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient u x) ≤ B)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F (s, x))
      (H.connection.laplacian (fun y => F (t, y)) x) t)
    (hrep : ∀ t, 0 < t → ∀ x,
      F (t, x) = ∫ y, u y * H.kernel x y t ∂g.volumeMeasure)
    (hzero : ∀ x, F (0, x) = u x)
    (hqc : ContinuousOn (fun p : ℝ × M => g.inner p.2
      (H.connection.gradient (fun y => F (p.1, y)) p.2)
      (H.connection.gradient (fun y => F (p.1, y)) p.2)) (Icc 0 1 ×ˢ univ)) :
    ∀ t ∈ Icc 0 1, ∀ x,
      g.tangentNorm x (H.connection.gradient (fun y => F (t, y)) x) ≤
        Real.sqrt (B ^ 2 + 1) * Real.exp (((n : ℝ) - 1) * K) := by
  have hLip : ∀ x y, |u y - u x| ≤ (B + 1) * (g.edist x y).toReal := by
    intro x y
    rw [abs_sub_comm]
    exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hu.of_le (by simp)) (K := ⟨B + 1, by positivity⟩) (by change 0 < B + 1; positivity)
      (fun z => (H.connection.gradient_norm_le_iff u z (by positivity : 0 ≤ B + 1)).mp
        ((hgrad z).trans (by linarith))) x y
  obtain ⟨A, hA⟩ := huc.exists_bound_of_continuous hu.continuous
  have hA0 : 0 ≤ A := (norm_nonneg (u O)).trans (hA O)
  have hb : ∀ t ∈ Icc 0 1, ∀ x, |F (t, x)| ≤ (g.edist O x).toReal + A := by
    intro t ht x
    have hval : |F (t, x)| ≤ A := by
      rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · rw [← ht0, hzero]
        exact hA x
      · rw [hrep t ht0]
        have h := norm_integral_le_of_norm_le (f := fun y => u y * H.kernel x y t)
          ((H.integrable_kernel x ht0).const_mul A)
          (ae_of_all _ (fun y => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (H.positive x y t ht0)]
            exact mul_le_mul_of_nonneg_right (hA y) (H.positive x y t ht0).le))
        rwa [integral_const_mul, H.mass_one x t ht0, mul_one] at h
    exact hval.trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  obtain ⟨V, c, hV, hvol⟩ :=
    g.exists_exponential_volume_bound_of_abs_sectionalCurvature_le H.connection hn hc hK hsec O
  have hi := H.connection.integrable_gaussian_heat_energy hc O hF
    (H.continuousOn_kernel_evolution hu.continuous (by positivity : 0 ≤ B + 1)
      hLip hF.continuousOn hrep hzero) hheat hA0 zero_lt_one hV
      (by norm_num : (0 : ℝ) < 1 / 32) hb hvol
  apply H.connection.heat_gradient_bound_of_gaussian_energy_of_initial_bound hc O
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hn)) hK) hF hheat _ hqc _ hi
  · intro t ht x
    simpa only [neg_mul] using
      H.connection.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le
        x K (hsec x) (H.connection.gradient (fun y => F (t, y)) x)
  · intro x
    rw [show (fun y => F (0, y)) = u from funext hzero]
    have hq : 0 ≤ g.inner x (H.connection.gradient u x) (H.connection.gradient u x) := by
      by_cases h : H.connection.gradient u x = 0
      · simp [h]
      · exact (g.pos x _ h).le
    have h := hgrad x
    change Real.sqrt _ ≤ B at h
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg
      (g.inner x (H.connection.gradient u x) (H.connection.gradient u x))]

theorem kernel_evolution_gradient_bound_of_compact_initial_regularity
    (H : ConservativeHeatKernelData g) (hn : 1 ≤ n) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K) (O : M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient f x) ≤ 2)
    (hcompact : ∀ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u → HasCompactSupport u →
      ∃ G : ℝ × M → ℝ,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ G (Ioi 0 ×ˢ univ) ∧
        (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => G (s, x))
          (H.connection.laplacian (fun y => G (t, y)) x) t) ∧
        (∀ t, 0 < t → ∀ x, G (t, x) = ∫ y, u y * H.kernel x y t ∂g.volumeMeasure) ∧
        (∀ x, G (0, x) = u x) ∧
        ContinuousOn (fun p : ℝ × M => g.inner p.2
          (H.connection.gradient (fun y => G (p.1, y)) p.2)
          (H.connection.gradient (fun y => G (p.1, y)) p.2)) (Icc 0 1 ×ˢ univ))
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hrep : ∀ t, 0 < t → ∀ x,
      F (t, x) = ∫ y, f y * H.kernel x y t ∂g.volumeMeasure) :
    ∀ t ∈ Ioc 0 1, ∀ x,
      g.tangentNorm x (H.connection.gradient (fun y => F (t, y)) x) ≤
        Real.sqrt ((2 + 6 * heatCutoffConstant) ^ 2 + 1) *
          Real.exp (((n : ℝ) - 1) * K) := by
  let B : ℝ := 2 + 6 * heatCutoffConstant
  have hB : 0 ≤ B := by
    have := heatCutoffConstant_pos
    dsimp [B]
    positivity
  let C : ℝ := Real.sqrt (B ^ 2 + 1) * Real.exp (((n : ℝ) - 1) * K)
  have hC : 0 < C := mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)
  intro t ht x
  have hslice : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y)) := by
    intro y
    exact (hF.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (t, y) ∈ Ioi 0 ×ˢ univ from ⟨ht.1, mem_univ y⟩))).comp y
        (contMDiffAt_const.prodMk contMDiffAt_id)
  have heq : (fun y => F (t, y)) =
      (fun z => ∫ y, f y * H.kernel z y t ∂g.volumeMeasure) := funext (hrep t ht.1)
  rw [heq] at hslice ⊢
  apply H.kernel_integral_gradient_bound_of_compact_evolutions hc O hf happrox hgrad
    (C := ⟨C, hC.le⟩) hC ht.1 _ ((hslice x).mdifferentiableAt (by simp))
  intro u hu huc hug
  obtain ⟨G, hG, hheat, hGrep, hzero, hqc⟩ := hcompact u hu huc
  have hGs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => G (t, y)) := by
    intro y
    exact (hG.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (t, y) ∈ Ioi 0 ×ˢ univ from ⟨ht.1, mem_univ y⟩))).comp y
        (contMDiffAt_const.prodMk contMDiffAt_id)
  have hGeq : (fun z => G (t, z)) =
      (fun z => ∫ y, u y * H.kernel z y t ∂g.volumeMeasure) := funext (hGrep t ht.1)
  have hb := H.compact_kernel_evolution_gradient_bound hn hc hK hsec O hu huc hB
    hug hG hheat hGrep hzero hqc t ⟨ht.1.le, ht.2⟩
  rw [hGeq] at hGs hb
  exact ⟨hGs.of_le (by simp), hb⟩

theorem compact_initial_regularity_of_exhaustion_integral_heat_equation
    [NeZero n]
    (H : ConservativeHeatKernelData g) (hn : 1 ≤ n) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ t, 0 < t → ∀ x y, H.kernel x y t =
      LeviCivitaData.dirichletExhaustionKernel
        (fun j => LeviCivitaData.Dirichlet.heatKernelContinuousTime H.connection (S j))
        t x y)
    (hheat : ∀ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u → HasCompactSupport u →
      ∀ t, 0 < t → ∀ x, HasDerivAt
        (fun s => ∫ y, u y * H.kernel x y s ∂g.volumeMeasure)
        (H.connection.laplacian
          (fun z => ∫ y, u y * H.kernel z y t ∂g.volumeMeasure) x) t) :
    ∀ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u → HasCompactSupport u →
      ∃ G : ℝ × M → ℝ,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ G (Ioi 0 ×ˢ univ) ∧
        (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => G (s, x))
          (H.connection.laplacian (fun y => G (t, y)) x) t) ∧
        (∀ t, 0 < t → ∀ x, G (t, x) = ∫ y, u y * H.kernel x y t ∂g.volumeMeasure) ∧
        (∀ x, G (0, x) = u x) ∧
        ContinuousOn (fun p : ℝ × M => g.inner p.2
          (H.connection.gradient (fun y => G (p.1, y)) p.2)
          (H.connection.gradient (fun y => G (p.1, y)) p.2)) (Icc 0 1 ×ˢ univ) := by
  let k : ℝ := ((n : ℝ) - 1) * K
  have hk : 0 ≤ k := mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hn)) hK
  have hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ H.connection.ricci x v v := by
    intro x v
    simpa only [k, neg_mul] using
      H.connection.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K (hsec x) v
  intro u hu huc
  let G := LeviCivitaData.Dirichlet.compactInitialEvolution H.connection S u
  have hG := LeviCivitaData.Dirichlet.contMDiffOn_compactInitialEvolution
    H.connection hc hk hRic S hΩmono hcover hu huc
  have hrep : ∀ t, 0 < t → ∀ x,
      G (t, x) = ∫ y, u y * H.kernel x y t ∂g.volumeMeasure := by
    intro t ht x
    rw [show G (t, x) = _ from
      LeviCivitaData.Dirichlet.compactInitialEvolution_of_pos H.connection S u ht x]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => congrArg (u y * ·) (hkernel t ht x y).symm)
  refine ⟨G, hG, ?_, hrep,
    LeviCivitaData.Dirichlet.compactInitialEvolution_zero H.connection S u, ?_⟩
  · intro t ht x
    have h := hheat u hu huc t ht x
    rw [show (fun y => G (t, y)) =
      (fun z => ∫ y, u y * H.kernel z y t ∂g.volumeMeasure) from funext (hrep t ht)]
    apply h.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact hrep s hs x
  · exact (LeviCivitaData.Dirichlet.continuousOn_compactInitialEvolution_gradient_normSq
      H.connection hc hk hRic S hΩmono hcover hu huc).mono
        (prod_mono Icc_subset_Ici_self subset_rfl)

theorem kernel_evolution_gradient_bound_of_exhaustion_integral_heat_equation
    [NeZero n]
    (H : ConservativeHeatKernelData g) (hn : 1 ≤ n) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K) (O : M)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ t, 0 < t → ∀ x y, H.kernel x y t =
      LeviCivitaData.dirichletExhaustionKernel
        (fun j => LeviCivitaData.Dirichlet.heatKernelContinuousTime H.connection (S j))
        t x y)
    (hheat : ∀ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u → HasCompactSupport u →
      ∀ t, 0 < t → ∀ x, HasDerivAt
        (fun s => ∫ y, u y * H.kernel x y s ∂g.volumeMeasure)
        (H.connection.laplacian
          (fun z => ∫ y, u y * H.kernel z y t ∂g.volumeMeasure) x) t)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient f x) ≤ 2)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hrep : ∀ t, 0 < t → ∀ x,
      F (t, x) = ∫ y, f y * H.kernel x y t ∂g.volumeMeasure) :
    ∀ t ∈ Ioc 0 1, ∀ x,
      g.tangentNorm x (H.connection.gradient (fun y => F (t, y)) x) ≤
        Real.sqrt ((2 + 6 * heatCutoffConstant) ^ 2 + 1) *
          Real.exp (((n : ℝ) - 1) * K) := by
  exact H.kernel_evolution_gradient_bound_of_compact_initial_regularity hn hc hK hsec O
    hf happrox hgrad (H.compact_initial_regularity_of_exhaustion_integral_heat_equation
      hn hc hK hsec S hΩmono hcover hkernel hheat) hF hrep

theorem compact_initial_regularity_of_exhaustion_kernel
    [NeZero n]
    (H : ConservativeHeatKernelData g) (hn : 1 ≤ n) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ t, 0 < t → ∀ x y, H.kernel x y t =
      LeviCivitaData.dirichletExhaustionKernel
        (fun j => LeviCivitaData.Dirichlet.heatKernelContinuousTime H.connection (S j))
        t x y) :
    ∀ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u → HasCompactSupport u →
      ∃ G : ℝ × M → ℝ,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ G (Ioi 0 ×ˢ univ) ∧
        (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => G (s, x))
          (H.connection.laplacian (fun y => G (t, y)) x) t) ∧
        (∀ t, 0 < t → ∀ x, G (t, x) = ∫ y, u y * H.kernel x y t ∂g.volumeMeasure) ∧
        (∀ x, G (0, x) = u x) ∧
        ContinuousOn (fun p : ℝ × M => g.inner p.2
          (H.connection.gradient (fun y => G (p.1, y)) p.2)
          (H.connection.gradient (fun y => G (p.1, y)) p.2)) (Icc 0 1 ×ˢ univ) := by
  apply H.compact_initial_regularity_of_exhaustion_integral_heat_equation
    hn hc hK hsec S hΩmono hcover hkernel
  let k : ℝ := ((n : ℝ) - 1) * K
  have hk : 0 ≤ k := mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hn)) hK
  have hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ H.connection.ricci x v v := by
    intro x v
    simpa only [k, neg_mul] using
      H.connection.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K (hsec x) v
  intro u hu huc t ht x
  have h := LeviCivitaData.Dirichlet.hasDerivAt_dirichletExhaustionKernel_integral_laplacian
    H.connection hc hk hRic S hΩmono hcover hu huc ht x
  simp_rw [hkernel t ht]
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr
  simp_rw [hkernel r hr]

theorem kernel_evolution_gradient_bound_of_exhaustion_kernel
    [NeZero n]
    (H : ConservativeHeatKernelData g) (hn : 1 ≤ n) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K) (O : M)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ t, 0 < t → ∀ x y, H.kernel x y t =
      LeviCivitaData.dirichletExhaustionKernel
        (fun j => LeviCivitaData.Dirichlet.heatKernelContinuousTime H.connection (S j))
        t x y)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient f x) ≤ 2)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hrep : ∀ t, 0 < t → ∀ x,
      F (t, x) = ∫ y, f y * H.kernel x y t ∂g.volumeMeasure) :
    ∀ t ∈ Ioc 0 1, ∀ x,
      g.tangentNorm x (H.connection.gradient (fun y => F (t, y)) x) ≤
        Real.sqrt ((2 + 6 * heatCutoffConstant) ^ 2 + 1) *
          Real.exp (((n : ℝ) - 1) * K) := by
  exact H.kernel_evolution_gradient_bound_of_compact_initial_regularity hn hc hK hsec O
    hf happrox hgrad (H.compact_initial_regularity_of_exhaustion_kernel
      hn hc hK hsec S hΩmono hcover hkernel) hF hrep

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
