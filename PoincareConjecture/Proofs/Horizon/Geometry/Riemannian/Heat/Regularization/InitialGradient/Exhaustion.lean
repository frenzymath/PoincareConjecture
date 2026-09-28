import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary DirichletExhaustion

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem tendsto_integral_exhaustion_compact_data
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {f : M → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (x : M) :
    Tendsto (fun j => ∫ y, heatKernelContinuousTime D (S j) t x y * f y ∂g.volumeMeasure)
      atTop (𝓝 (∫ y, dirichletExhaustionKernel
        (fun j => heatKernelContinuousTime D (S j)) t x y * f y ∂g.volumeMeasure)) := by
  let K := fun j => heatKernelContinuousTime D (S j)
  have hK := fun j => heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  have hm := fun (t : ℝ) (ht : 0 < t) (x y : M) =>
    D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y
  have hb := fun (t : ℝ) (ht : 0 < t) (x y : M) => D.bddAbove_heatKernelContinuousTime_exhaustion
    (Nat.pos_of_ne_zero (NeZero.ne n)) hc hk hRic S hΩmono hcover ht x y
  obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf
  apply tendsto_integral_of_dominated_convergence
    (fun y => B * dirichletExhaustionKernel K t x y)
  · intro j
    exact (((hK j).integrable_ambient ht x).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  · exact (mass hK hm hb ht x).1.const_mul B
  · intro j
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hK j).nonneg t ht x y)]
    calc
      _ ≤ K j t x y * B := mul_le_mul_of_nonneg_left (hB y) ((hK j).nonneg t ht x y)
      _ ≤ dirichletExhaustionKernel K t x y * B :=
        mul_le_mul_of_nonneg_right (le_supremum hb j ht x y)
          ((norm_nonneg (f y)).trans (hB y))
      _ = _ := mul_comm _ _
  · exact ae_of_all _ fun y => (tendsto_supremum hm hb ht x y).mul_const (f y)

theorem exists_exhaustion_integral_initial_fderiv_bound
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V K : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVs : closure V ⊆ e.source) (hK : IsCompact K) (hKV : K ⊆ V)
    (hconv : Convex ℝ K)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, 0 < t → ∀ x ∈ interior K,
      ‖fderiv ℝ (fun z => (∫ y, dirichletExhaustionKernel
        (fun j => heatKernelContinuousTime D (S j)) t (e z) y * f y ∂g.volumeMeasure) -
        f (e z)) x‖ ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := exists_heat_test_initial_coordinate_jet_bound
    D e he hei hV hVc hVs hK hKV f 1
  have hcompact : IsCompact (tsupport f ∪ e '' closure V) :=
    hfc.isCompact.union (hVc.image_of_continuousOn (e.continuousOn.mono hVs))
  obtain ⟨j₀, hj₀⟩ := hcompact.elim_directed_cover Ω (fun j => (S j).isOpen)
    (by rw [hcover]; exact subset_univ _) hΩmono.directed_le
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  let L : ℝ≥0 := ⟨C * t, mul_nonneg hC.le ht.le⟩
  let U := fun j z =>
    (∫ y, heatKernelContinuousTime D (S j) t (e z) y * f y ∂g.volumeMeasure) - f (e z)
  let F := fun z => (∫ y, dirichletExhaustionKernel
    (fun j => heatKernelContinuousTime D (S j)) t (e z) y * f y ∂g.volumeMeasure) - f (e z)
  have hlimit (z : E) : Tendsto (fun j => U j z) atTop (𝓝 (F z)) :=
    (tendsto_integral_exhaustion_compact_data D hc hk hRic S hΩmono hcover
      hf.continuous hfc ht (e z)).sub_const (f (e z))
  have hLip : ∀ᶠ j in atTop, LipschitzOnWith L (U j) K := by
    filter_upwards [eventually_ge_atTop j₀] with j hj
    have hcontain := hj₀.trans (hΩmono hj)
    let φ : EnergyTest D (Ω j) := ⟨f, hf, hfc, fun y hy => hcontain (Or.inl hy)⟩
    have hVΩ : e '' V ⊆ Ω j := fun y hy => hcontain (Or.inr ((image_mono subset_closure) hy))
    have hrep (z : E) : U j z =
        heatPowerContinuous D (S j) 0 t ht (toDomainL2 D (Ω j) (φ : H1Zero D (Ω j)))
          (e z) - f (e z) := by
      dsimp [U]
      congr 1
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω j) (fun y hy => by
        rw [(heatKernelContinuousTime_isDirichletHeatKernel D (S j)).zero_outside
          t ht (e z) y (Or.inr hy), zero_mul])]
      simp only [heatKernelContinuousTime_of_pos D (S j) ht]
      exact integral_heatKernelContinuous_test D (S j) t ht (e z) φ
    have hsmooth : ContDiffOn ℝ ∞ (U j) V := by
      rw [show U j = _ from funext hrep]
      apply contMDiffOn_iff_contDiffOn.mp
      exact ((contMDiffOn_heatPowerContinuous D (S j) 0 t ht _).sub hf.contMDiffOn).comp
        (he.mono (subset_closure.trans hVs)) (fun z hz => hVΩ ⟨z, hz, rfl⟩)
    apply hconv.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hsmooth.contDiffAt (hV.mem_nhds (hKV hz))).differentiableAt (by simp))
    intro z hz
    change ‖fderiv ℝ (U j) z‖ ≤ C * t
    rw [show U j = _ from funext hrep]
    simpa only [norm_iteratedFDeriv_one] using hbound (S j) hVΩ φ rfl ht z hz
  have hLipLimit : LipschitzOnWith L F K := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro y hy z hz
    apply le_of_tendsto ((hlimit y).dist (hlimit z))
    filter_upwards [hLip] with j hj
    exact hj.dist_le_mul y hy z hz
  exact norm_fderiv_le_of_lipschitzOn ℝ (mem_interior_iff_mem_nhds.mp hx) hLipLimit

end PoincareConjecture.LeviCivitaData.Dirichlet
