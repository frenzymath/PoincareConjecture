import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.CompactIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Equation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace Poincare.Analysis.Heat



theorem integral_mul_kernel_swap
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsFiniteMeasureOnCompacts μ]
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    {H : M → M → ℝ} (hH : Continuous (Function.uncurry H)) :
    (∫ x, u x * (∫ y, v y * H x y ∂μ) ∂μ) =
      ∫ y, v y * (∫ x, u x * H x y ∂μ) ∂μ := by
  have hcont : Continuous (Function.uncurry (fun x y => u x * (v y * H x y))) :=
    (hu.comp continuous_fst).mul ((hv.comp continuous_snd).mul hH)
  have hcomp : HasCompactSupport
      (Function.uncurry (fun x y => u x * (v y * H x y))) := by
    apply HasCompactSupport.intro (huc.prod hvc)
    intro p hp
    by_cases hx : p.1 ∈ tsupport u
    · have hy : p.2 ∉ tsupport v := fun hy => hp ⟨hx, hy⟩
      simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hx]
  calc
    _ = ∫ x, ∫ y, u x * (v y * H x y) ∂μ ∂μ := by
      simp only [integral_const_mul]
    _ = ∫ y, ∫ x, u x * (v y * H x y) ∂μ ∂μ :=
      integral_integral_swap_of_hasCompactSupport hcont hcomp
    _ = _ := by
      simp only [mul_left_comm (u _) (v _), integral_const_mul]

end Poincare.Analysis.Heat

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}



theorem hasDerivAt_dirichletExhaustionKernel_integral_laplacian
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 < t) (x : M) :
    HasDerivAt
      (fun r => ∫ y, u y * dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) r x y ∂g.volumeMeasure)
      (D.laplacian (fun z => ∫ y, u y * dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) t z y ∂g.volumeMeasure) x) t := by
  let H := dirichletExhaustionKernel (fun q => heatKernelContinuousTime D (S q))
  let F : ℝ × M → ℝ := fun p => ∫ y, u y * H p.1 p.2 y ∂g.volumeMeasure
  have hF := contMDiffOn_dirichletExhaustionKernel_integral
    D hc hk hRic S hΩmono hcover hu huc
  have hHs := contMDiffOn_dirichletExhaustionKernel D hc hk hRic S hΩmono hcover
  have hHc (r : ℝ) (hr : 0 < r) : Continuous (fun p : M × M => H r p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hmap : ContinuousAt (fun q : M × M => ((r, q.1), q.2)) p :=
      (continuousAt_const.prodMk continuousAt_fst).prodMk continuousAt_snd
    have hlocal := (hHs.contMDiffAt (x := ((r, p.1), p.2))
      (((isOpen_Ioi.prod isOpen_univ).prod isOpen_univ).mem_nhds
        ⟨⟨hr, mem_univ p.1⟩, mem_univ p.2⟩)).continuousAt.comp
          (f := fun q : M × M => ((r, q.1), q.2)) hmap
    exact hlocal
  have hsymm (r : ℝ) (hr : 0 < r) (a b : M) : H r a b = H r b a :=
    DirichletExhaustion.symmetric
      (fun q => heatKernelContinuousTime_isDirichletHeatKernel D (S q)) hr a b
  apply D.hasDerivAt_of_smooth_weak_heatEquation hF ht _ x
  intro φ hφ hφc
  let G : ℝ × M → ℝ := fun p => ∫ y, φ y * H p.1 y p.2 ∂g.volumeMeasure
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ G
      (Ioi 0 ×ˢ univ) := by
    apply (contMDiffOn_dirichletExhaustionKernel_integral
      D hc hk hRic S hΩmono hcover hφ hφc).congr
    intro p hp
    apply integral_congr_ae
    exact ae_of_all _ (fun y => congrArg (φ y * ·) (hsymm p.1 hp.1 y p.2))
  have htime := hasDerivAt_integral_test_mul (g := g) hG hu.continuous huc ht
  have hderiv (y : M) : deriv (fun r => G (r, y)) t =
      ∫ z, H t z y * D.laplacian φ z ∂g.volumeMeasure :=
    (hasDerivAt_integral_test_mul_dirichletExhaustionKernel
      D hc hk hRic S hΩmono hcover y hφ hφc ht).deriv
  have hpair : (fun r => ∫ z, φ z * F (r, z) ∂g.volumeMeasure) =ᶠ[𝓝 t]
      (fun r => ∫ y, u y * G (r, y) ∂g.volumeMeasure) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr
    exact Poincare.Analysis.Heat.integral_mul_kernel_swap
      hφ.continuous hu.continuous hφc huc (hHc r hr)
  have hvalue : (∫ y, u y * deriv (fun r => G (r, y)) t ∂g.volumeMeasure) =
      ∫ z, F (t, z) * D.laplacian φ z ∂g.volumeMeasure := by
    simp_rw [hderiv]
    calc
      _ = ∫ y, u y * (∫ z, D.laplacian φ z * H t z y ∂g.volumeMeasure)
          ∂g.volumeMeasure := by simp only [mul_comm (H t _ _)]
      _ = ∫ z, D.laplacian φ z * (∫ y, u y * H t z y ∂g.volumeMeasure)
          ∂g.volumeMeasure :=
        (Poincare.Analysis.Heat.integral_mul_kernel_swap
          (H := H t)
          (D.continuous_laplacian hφ) hu.continuous
          (D.hasCompactSupport_laplacian hφc) huc (hHc t ht)).symm
      _ = _ := by simp only [F, mul_comm]
  rw [hvalue] at htime
  exact htime.congr_of_eventuallyEq hpair

end PoincareConjecture.LeviCivitaData.Dirichlet
