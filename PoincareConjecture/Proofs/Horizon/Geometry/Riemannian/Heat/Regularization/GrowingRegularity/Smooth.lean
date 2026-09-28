import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.KernelIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.LiftDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

theorem contMDiffOn_integral_of_exhaustion_kernel
    (H : ConservativeHeatKernelData g) (hn : 2 ≤ n)
    (D : LeviCivitaData g) (hc : MetricComplete g) {K : ℝ} (hK : 0 < K)
    (hsec : ∀ x v w, |D.sectionalCurvature x v w| ≤ K)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (hkernel : ∀ x y t, H.kernel x y t = LeviCivitaData.dirichletExhaustionKernel
      (fun j => LeviCivitaData.Dirichlet.heatKernelContinuousTime D (S j)) t x y)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ}
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
      (Ioi 0 ×ˢ univ) := by
  let k : ℝ := ((n : ℝ) - 1) * K
  have hk : 0 ≤ k := mul_nonneg (sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ n))) hK.le
  have hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v := by
    intro x v
    simpa only [k, neg_mul] using
      D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K (hsec x) v
  obtain ⟨r, C, A, hr, hC, hA, hlift⟩ := exists_uniform_harmonic_lift hn hK
  intro p hp
  obtain ⟨F⟩ := hlift g D hc hsec p.2
  have hF := F.contDiffOn_kernel_integral hr hC hA.le H D hc hk hRic
    S hΩmono hcover hkernel hf hLip
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 r := by
    simpa using hr
  have hFat := hF.contDiffAt (x := (0, p.1))
    ((Metric.isOpen_ball.prod isOpen_Ioi).mem_nhds ⟨hzero, hp.1⟩)
  exact (F.contMDiffAt_of_contDiffAt_pullback hr
    (u := fun q : ℝ × M => ∫ y, f y * H.kernel q.2 y q.1 ∂g.volumeMeasure)
    (t := p.1) hFat).contMDiffWithinAt

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
