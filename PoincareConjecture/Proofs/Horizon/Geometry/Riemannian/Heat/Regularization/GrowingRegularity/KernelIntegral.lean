import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.InteriorJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.HarmonicCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingData
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.CompactIntegral











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric.UniformHarmonicLift

open LeviCivitaData Poincare.Parabolic.Interior

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem contDiffOn_kernel_integral
    {O : M} {r C A : ℝ} (F : UniformHarmonicLift g O r C A)
    (hr : 0 < r) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (H : ConservativeHeatKernelData g) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (hkernel : ∀ x y t, H.kernel x y t = dirichletExhaustionKernel
      (fun q => Dirichlet.heatKernelContinuousTime D (S q)) t x y)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ}
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal) :
    ContDiffOn ℝ ∞
      (fun p : E × ℝ => ∫ y, f y * H.kernel (F.e p.1) y p.2 ∂g.volumeMeasure)
      (Metric.ball 0 r ×ˢ Ioi 0) := by
  let : SecondCountableTopology M := g.secondCountableTopology
  let U : Set (E × ℝ) := Metric.ball 0 r ×ˢ Ioi 0
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioi
  have hsmall : Metric.ball (0 : E) r ⊆ Metric.ball 0 (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hH := Dirichlet.contMDiffOn_dirichletExhaustionKernel D hc hk hRic S hΩmono hcover
  have hparam : ContMDiffOn (𝓘(ℝ, E × ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun q : (E × ℝ) × M => H.kernel (F.e q.1.1) q.2 q.1.2) (U ×ˢ univ) := by
    intro q hq
    have he := F.he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsmall hq.1.1))
    have ht : ContMDiffAt (𝓘(ℝ, E × ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun w : (E × ℝ) × M => w.1.2) q :=
      contDiffAt_snd.contMDiffAt.comp q contMDiffAt_fst
    have hx : ContMDiffAt (𝓘(ℝ, E × ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun w : (E × ℝ) × M => w.1.1) q :=
      contDiffAt_fst.contMDiffAt.comp q contMDiffAt_fst
    have hm := (ht.prodMk (he.comp q hx)).prodMk contMDiffAt_snd
    have hs := hH.contMDiffAt
      (((isOpen_Ioi.prod isOpen_univ).prod isOpen_univ).mem_nhds
        (show ((q.1.2, F.e q.1.1), q.2) ∈ ((Ioi 0 ×ˢ univ) ×ˢ univ) from
          ⟨⟨hq.1.2, mem_univ _⟩, mem_univ _⟩))
    have hh := (hs.comp q hm).contMDiffWithinAt (s := U ×ˢ univ)
    simpa only [Function.comp_def, hkernel] using hh
  apply (H.contDiffOn_integral_of_kernel_derivative_bounds hf hLip hU ?_ ?_ ?_).1
  · intro y
    have hs := F.contDiffOn_exhaustionKernel_pullback D hc hk hRic S hΩmono hcover y
    simpa only [hkernel] using hs.mono (prod_mono hsmall (subset_refl _))
  · intro m z hz
    have hj := (Poincare.Analysis.Heat.contMDiffOn_iteratedFDeriv_parameter hU hparam m).continuousOn
    have hjc : Continuous (fun y => iteratedFDeriv ℝ m
        (fun w : E × ℝ => H.kernel (F.e w.1) y w.2) z) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      have hh := hj.continuousAt (x := (z, y))
        ((hU.prod isOpen_univ).mem_nhds (show (z, y) ∈ U ×ˢ univ from ⟨hz, mem_univ y⟩))
      exact hh.comp (f := fun y : M => (z, y)) (continuousAt_const.prodMk continuousAt_id)
    exact hjc.aestronglyMeasurable
  · intro z hz m
    have hz0 : 0 < z.2 := hz.2
    have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
    let G : ℝ := (A * Real.sqrt (2 * (2 * r))) / (C⁻¹) ^ 2
    have hG : 0 ≤ G := by dsimp [G]; positivity
    have hinv : (1 : ℝ) / C ≤ C :=
      (one_div_le_one_div_of_le zero_lt_one hC).trans (by simpa using hC)
    obtain ⟨J, hJ, hjet⟩ := exists_static_heat_spacetime_jet_bound
      (lam := 1 / C) (Λ := C) (H := G) (by positivity) hinv hG
      (r := r) (R := 2 * r) (α := z.2 / 4) (β := z.2 + 2)
      (a := z.2 / 2) (b := z.2 + 1) hr.le (by linarith) (by linarith)
      (by linarith) (by linarith) F.h.principalOperator
      F.h.contDiff_principalOperator.contDiffOn
      (fun x _ => F.h.principalOperator_symmetric x)
      (fun x hx => F.principalOperator_elliptic_bounds hC0 hx)
      (fun x hx y hy => F.principalOperator_holder_bound hC0 hA hx hy) m
    obtain ⟨B, hB, hvalue⟩ := F.exists_exhaustionKernel_pullback_bound
      D hc hk hRic S hΩmono hcover (a := z.2 / 4) (b := z.2 + 2)
      (by linarith) (by linarith)
    let V : Set (E × ℝ) := univ ×ˢ Ioo (z.2 / 2) (z.2 + 1)
    have hV : V ∈ 𝓝 z := (isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ _, by constructor <;> linarith⟩
    refine ⟨V, hV, J * B, O, (z.2 + 2) + 1, by linarith, ?_⟩
    intro y w hw
    have ht : 0 < (z.2 + 2) + 1 := by linarith
    have hamp : 0 ≤ B * dirichletExhaustionKernel
        (fun q => Dirichlet.heatKernelContinuousTime D (S q)) ((z.2 + 2) + 1) O y := by
      rw [← hkernel]
      exact mul_nonneg hB.le (H.positive O y _ ht).le
    have hs := F.contDiffOn_exhaustionKernel_pullback D hc hk hRic S hΩmono hcover y
    have he := hjet _ hamp
      (fun p : E × ℝ => dirichletExhaustionKernel
        (fun q => Dirichlet.heatKernelContinuousTime D (S q)) p.2 (F.e p.1) y)
      (hs.mono (prod_mono (subset_refl _) (fun t ht => by
        have hα : 0 < z.2 / 4 := by linarith
        exact hα.trans ht.1)))
      (fun x hx t ht => F.timeDerivative_exhaustionKernel_pullback
        D hc hk hRic S hΩmono hcover y hx (by
          have hα : 0 < z.2 / 4 := by linarith
          exact hα.trans ht.1))
      (fun x hx t ht => hvalue t ⟨ht.1.le, ht.2.le⟩ x hx y)
      w ⟨Metric.ball_subset_closedBall hw.2.1, hw.1.2.1.le, hw.1.2.2.le⟩
    simpa only [hkernel, mul_assoc] using he

end PoincareConjecture.RiemannianMetric.UniformHarmonicLift
