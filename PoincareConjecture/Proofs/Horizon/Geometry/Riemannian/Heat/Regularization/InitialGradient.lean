import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.CompactIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.Continuity

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def compactInitialEvolution (D : LeviCivitaData g) {Ω : ℕ → Set M}
    (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j)) (f : M → ℝ)
    (p : ℝ × M) : ℝ :=
  if 0 < p.1 then ∫ y, f y * dirichletExhaustionKernel
    (fun j => heatKernelContinuousTime D (S j)) p.1 p.2 y ∂g.volumeMeasure
  else f p.2

@[simp] theorem compactInitialEvolution_zero (D : LeviCivitaData g) {Ω : ℕ → Set M}
    (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j)) (f : M → ℝ) (x : M) :
    compactInitialEvolution D S f (0, x) = f x := by
  simp [compactInitialEvolution]

theorem compactInitialEvolution_of_pos (D : LeviCivitaData g) {Ω : ℕ → Set M}
    (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j)) (f : M → ℝ)
    {t : ℝ} (ht : 0 < t) (x : M) :
    compactInitialEvolution D S f (t, x) = ∫ y, f y * dirichletExhaustionKernel
      (fun j => heatKernelContinuousTime D (S j)) t x y ∂g.volumeMeasure := by
  simp [compactInitialEvolution, ht]

variable [PreconnectedSpace M]

theorem contMDiffOn_compactInitialEvolution
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfc : HasCompactSupport f) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (compactInitialEvolution D S f) (Ioi 0 ×ˢ univ) := by
  apply (contMDiffOn_dirichletExhaustionKernel_integral D hc hk hRic S hΩmono hcover
    hf hfc).congr
  intro p hp
  exact compactInitialEvolution_of_pos D S f hp.1 p.2

theorem continuousOn_compactInitialEvolution_gradient_normSq
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfc : HasCompactSupport f) :
    ContinuousOn (fun p : ℝ × M => g.inner p.2
      (D.gradient (fun y => compactInitialEvolution D S f (p.1, y)) p.2)
      (D.gradient (fun y => compactInitialEvolution D S f (p.1, y)) p.2))
      (Ici 0 ×ˢ univ) := by
  have hF := contMDiffOn_compactInitialEvolution D hc hk hRic S hΩmono hcover hf hfc
  apply D.continuousOn_gradient_normSq_of_initial_chart_derivative hF hf
    (compactInitialEvolution_zero D S f)
  apply tendsto_initial_chart_derivative_of_exhaustion_integral D hc hk hRic S
    hΩmono hcover hf hfc hF
  intro t ht x
  rw [compactInitialEvolution_of_pos D S f ht]
  simp only [mul_comm]

end PoincareConjecture.LeviCivitaData.Dirichlet
