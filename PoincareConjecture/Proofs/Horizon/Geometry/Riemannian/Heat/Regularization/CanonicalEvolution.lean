import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.CanonicalKernel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.CompactData












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem kernel_integral_distance_lipschitz_of_exhaustion_kernel
    (H : ConservativeHeatKernelData g) (hn : 1 ≤ n) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K) (O : M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient f x) ≤ 2)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ t, 0 < t → ∀ x y, H.kernel x y t =
      LeviCivitaData.dirichletExhaustionKernel
        (fun j => LeviCivitaData.Dirichlet.heatKernelContinuousTime H.connection (S j))
        t x y) :
    ∀ t ∈ Ioc 0 1, ∀ x z,
      |(∫ y, f y * H.kernel x y t ∂g.volumeMeasure) -
        (∫ y, f y * H.kernel z y t ∂g.volumeMeasure)| ≤
        (Real.sqrt ((2 + 6 * heatCutoffConstant) ^ 2 + 1) *
          Real.exp (((n : ℝ) - 1) * K)) * (g.edist x z).toReal := by
  obtain ⟨u, hu, huc, hub, hug, hue⟩ :=
    H.connection.exists_compact_distance_approximations hc O hf happrox hgrad
  have hLip : ∀ x y, |f y - f x| ≤ 2 * (g.edist x y).toReal := by
    intro x y
    rw [abs_sub_comm]
    exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hf.of_le (by simp)) (K := 2) (by norm_num)
      (fun z => (H.connection.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z)) x y
  let B : ℝ := 2 + 6 * heatCutoffConstant
  have hB : 0 ≤ B := by
    have := heatCutoffConstant_pos
    dsimp [B]
    positivity
  let C : ℝ := Real.sqrt (B ^ 2 + 1) * Real.exp (((n : ℝ) - 1) * K)
  have hC : 0 < C := mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)
  intro t ht x z
  have hlim (w : M) : Tendsto
      (fun j => ∫ y, u j y * H.kernel w y t ∂g.volumeMeasure) atTop
      (𝓝 (∫ y, f y * H.kernel w y t ∂g.volumeMeasure)) := by
    apply H.tendsto_integral_of_dominated_initial_approximations hf.continuous hLip
      (fun j => (hu j).continuous) hub _ w ht.1
    intro y
    apply tendsto_const_nhds.congr'
    filter_upwards [hue y] with j hj
    exact hj.self_of_nhds.symm
  apply le_of_tendsto ((hlim x).sub (hlim z)).abs
  apply Eventually.of_forall
  intro j
  obtain ⟨G, hG, hheat, hrep, hzero, hqc⟩ :=
    H.compact_initial_regularity_of_exhaustion_kernel hn hc hK hsec
      S hΩmono hcover hkernel (u j) (hu j) (huc j)
  have hGs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => G (t, y)) := by
    intro y
    exact (hG.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (t, y) ∈ Ioi 0 ×ˢ univ from ⟨ht.1, mem_univ y⟩))).comp y
        (contMDiffAt_const.prodMk contMDiffAt_id)
  have hg := H.compact_kernel_evolution_gradient_bound hn hc hK hsec O
    (hu j) (huc j) hB (hug j) hG hheat hrep hzero hqc t ⟨ht.1.le, ht.2⟩
  have hbound := g.abs_sub_le_mul_toReal_edist_of_derivative_bound
    (hGs.of_le (by simp)) (K := (⟨C, hC.le⟩ : ℝ≥0)) hC
    (fun y => (H.connection.gradient_norm_le_iff (fun w => G (t, w)) y hC.le).mp
      (hg y)) x z
  change |G (t, x) - G (t, z)| ≤ C * (g.edist x z).toReal at hbound
  rw [hrep t ht.1 x, hrep t ht.1 z] at hbound
  exact hbound

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
