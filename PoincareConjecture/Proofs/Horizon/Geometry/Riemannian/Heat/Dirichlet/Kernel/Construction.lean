import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Equation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.StrictPositivity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.DomainMonotonicity

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

structure IsDirichletHeatKernel (D : LeviCivitaData g) (Ω : Set M)
    (K : ℝ → M → M → ℝ) : Prop where
  continuous : Continuous (fun p : (M × M) × Ioi (0 : ℝ) =>
    K p.2 p.1.1 p.1.2)
  smooth : ContMDiffOn (((𝓡 n).prod (𝓡 n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
    (fun p : (M × M) × ℝ => K p.2 p.1.1 p.1.2) ((Ω ×ˢ Ω) ×ˢ Ioi 0)
  nonneg : ∀ t, 0 < t → ∀ x y, 0 ≤ K t x y
  positive : ∀ t, 0 < t → ∀ x ∈ Ω, ∀ y ∈ Ω, 0 < K t x y
  zero_outside : ∀ t, 0 < t → ∀ x y, x ∉ Ω ∨ y ∉ Ω → K t x y = 0
  heat_equation : ∀ t, 0 < t → ∀ x ∈ Ω, ∀ y,
    HasDerivAt (fun s => K s x y) (D.laplacian (fun z => K t z y) x) t
  symmetric : ∀ t, 0 < t → ∀ x y, K t x y = K t y x
  semigroup : ∀ s t, 0 < s → 0 < t → ∀ x y,
    Integrable (fun z => K s x z * K t z y) (g.volumeMeasure.restrict Ω) ∧
    K (s + t) x y = ∫ z in Ω, K s x z * K t z y ∂g.volumeMeasure
  mass : ∀ t, 0 < t → ∀ x,
    Integrable (K t x) (g.volumeMeasure.restrict Ω) ∧
    (∫ y in Ω, K t x y ∂g.volumeMeasure) ≤ 1
  initial : ∀ φ : M → ℝ, ContinuousOn φ (closure Ω) → ∀ x ∈ Ω,
    Tendsto (fun t => ∫ y in Ω, K t x y * φ y ∂g.volumeMeasure)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (φ x))

theorem heatKernelContinuousTime_isDirichletHeatKernel (D : LeviCivitaData g)
    {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω) :
    IsDirichletHeatKernel D Ω (heatKernelContinuousTime D S) where
  continuous := by
    apply (continuous_heatKernelContinuous_joint D S).congr
    intro p
    exact (heatKernelContinuousTime_of_pos D S p.2.property p.1.1 p.1.2).symm
  smooth := contMDiffOn_heatKernelContinuousTime_joint D S
  nonneg := by
    intro t ht x y
    rw [heatKernelContinuousTime_of_pos D S ht]
    exact heatKernelContinuous_nonneg D S t ht x y
  positive := by
    intro t ht x hx y hy
    rw [heatKernelContinuousTime_of_pos D S ht]
    exact heatKernelContinuous_pos D S t ht x y hx hy
  zero_outside := by
    intro t ht x y h
    rw [heatKernelContinuousTime_of_pos D S ht]
    exact heatKernelContinuous_zero D S t ht x y h
  heat_equation := fun t ht x hx y =>
    hasDerivAt_heatKernelContinuousTime_laplacian D S t ht x y hx
  symmetric := by
    intro t ht x y
    simp only [heatKernelContinuousTime_of_pos D S ht]
    exact heatKernelContinuous_symm D S t ht x y
  semigroup := by
    intro s t hs ht x y
    simp only [heatKernelContinuousTime_of_pos D S hs,
      heatKernelContinuousTime_of_pos D S ht,
      heatKernelContinuousTime_of_pos D S (add_pos hs ht)]
    exact heatKernelContinuous_semigroup D S s t hs ht x y
  mass := by
    intro t ht x
    change Integrable (fun y => heatKernelContinuousTime D S t x y)
      (g.volumeMeasure.restrict Ω) ∧ _
    simp only [heatKernelContinuousTime_of_pos D S ht]
    exact ⟨integrable_heatKernelContinuous D S t ht x,
      heatKernelContinuous_mass_le_one D S t ht x⟩
  initial := fun _ hφ x hx => tendsto_integral_heatKernelContinuousTime D S hφ x hx

theorem exists_dirichletHeatKernels (D : LeviCivitaData g) :
    ∃ K : (Ω : Set M) → Poincare.Manifold.SmoothDomain n Ω → ℝ → M → M → ℝ,
      (∀ Ω S, IsDirichletHeatKernel D Ω (K Ω S)) ∧
      (∀ (Ω₁ Ω₂ : Set M) (S₁ : Poincare.Manifold.SmoothDomain n Ω₁)
        (S₂ : Poincare.Manifold.SmoothDomain n Ω₂), Ω₁ ⊆ Ω₂ →
        ∀ t, 0 < t → ∀ x ∈ Ω₁, ∀ y ∈ Ω₁,
          K Ω₁ S₁ t x y ≤ K Ω₂ S₂ t x y) := by
  refine ⟨fun _ S => heatKernelContinuousTime D S,
    fun _ S => heatKernelContinuousTime_isDirichletHeatKernel D S, ?_⟩
  intro Ω₁ Ω₂ S₁ S₂ h12 t ht x hx y hy
  simp only [heatKernelContinuousTime_of_pos D S₁ ht,
    heatKernelContinuousTime_of_pos D S₂ ht]
  exact heatKernelContinuous_domain_mono D S₁ S₂ h12 t ht x y hx hy

end PoincareConjecture.LeviCivitaData.Dirichlet
