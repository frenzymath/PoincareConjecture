import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.GlobalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Limit
import Mathlib.Topology.UniformSpace.Dini

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

theorem tendstoLocallyUniformlyOn_heatKernelContinuousTime_exhaustion
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ) (y : M) :
    TendstoLocallyUniformlyOn
      (fun q (p : ℝ × M) => heatKernelContinuousTime D (S q) p.1 p.2 y)
      (fun p : ℝ × M => dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) p.1 p.2 y)
      atTop (Ioi 0 ×ˢ univ) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · intro q
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hx : Continuous (fun p : (Ioi (0 : ℝ) ×ˢ (univ : Set M)) => p.1.2) :=
      continuous_snd.comp continuous_subtype_val
    have ht : Continuous (fun p : (Ioi (0 : ℝ) ×ˢ (univ : Set M)) =>
        (⟨p.1.1, p.2.1⟩ : Ioi (0 : ℝ))) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have hmap := (hx.prodMk (continuous_const (y := y))).prodMk ht
    have h := (heatKernelContinuousTime_isDirichletHeatKernel D (S q)).continuous.comp hmap
    exact h
  · intro p hp
    exact D.monotone_heatKernelContinuousTime_exhaustion S hΩmono hp.1 p.2 y
  · have hlim : ContinuousOn
        (fun p : (ℝ × M) × M => dirichletExhaustionKernel
          (fun q => heatKernelContinuousTime D (S q)) p.1.1 p.1.2 p.2)
        ((Ioi 0 ×ˢ univ) ×ˢ univ) :=
      (contMDiffOn_dirichletExhaustionKernel D hc hk hRic S hΩmono hcover).continuousOn
    have hmap : ContinuousOn (fun p : ℝ × M => (p, y)) (Ioi 0 ×ˢ univ) :=
      continuousOn_id.prodMk continuousOn_const
    have h := hlim.comp hmap (fun p hp => ⟨hp, mem_univ y⟩)
    exact h
  · intro p hp
    exact tendsto_atTop_ciSup
      (D.monotone_heatKernelContinuousTime_exhaustion S hΩmono hp.1 p.2 y)
      (D.bddAbove_heatKernelContinuousTime_exhaustion (NeZero.pos n) hc hk hRic
        S hΩmono hcover hp.1 p.2 y)

theorem hasDerivAt_integral_test_mul_dirichletExhaustionKernel
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ) (y : M)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => ∫ x, φ x * dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) r x y ∂g.volumeMeasure)
      (∫ x, dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) t x y *
          D.laplacian φ x ∂g.volumeMeasure) t := by
  apply D.hasDerivAt_integral_test_mul_of_exhaustion
    (F := fun q p => heatKernelContinuousTime D (S q) p.1 p.2 y)
    (fun q => (S q).isOpen) hΩmono hcover ?_ ?_
    (tendstoLocallyUniformlyOn_heatKernelContinuousTime_exhaustion
      D hc hk hRic S hΩmono hcover y) hφ hφc ht
  · intro q
    have hK := heatKernelContinuousTime_isDirichletHeatKernel D (S q)
    by_cases hy : y ∈ Ω q
    · intro p hp
      have hs := hK.smooth.contMDiffAt (x := ((p.2, y), p.1))
        ((((S q).isOpen.prod (S q).isOpen).prod isOpen_Ioi).mem_nhds
          ⟨⟨hp.2, hy⟩, hp.1⟩)
      exact (hs.comp p
        ((contMDiffAt_snd.prodMk contMDiffAt_const).prodMk contMDiffAt_fst)).contMDiffWithinAt
    · apply contMDiffOn_const.congr
      intro p hp
      exact hK.zero_outside p.1 hp.1 p.2 y (Or.inr hy)
  · intro q r hr x hx
    exact (heatKernelContinuousTime_isDirichletHeatKernel D (S q)).heat_equation r hr x hx y

end PoincareConjecture.LeviCivitaData.Dirichlet
