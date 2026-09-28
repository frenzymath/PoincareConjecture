import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.Transition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.BusemannWeakLaplacian













noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology
open Poincare.Riemannian.Soul

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M}



theorem integral_busemann_axialTransition_sub_nonneg
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hm : D.NonnegativeRicciCurvature)
    {ray : ℝ → M} (hray : IsRay ray)
    (N₁ N₂ : EpsilonNeck g)
    {A₁ B₁ A₂ B₂ : Set M} {φ₁ φ₂ : ℝ → ℝ}
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁)
    (hdisj₁ : Disjoint A₁ B₁) (hcover₁ : A₁ ∪ B₁ = N₁.central_sphereᶜ)
    (hneg₁ : N₁.region (-N₁.epsilon⁻¹) 0 ⊆ A₁)
    (hpos₁ : N₁.region 0 N₁.epsilon⁻¹ ⊆ B₁)
    {L₁ : ℝ} (hL₁ : 0 < L₁) (hLe₁ : L₁ < N₁.epsilon⁻¹)
    (hφ₁ : ContDiff ℝ ∞ φ₁)
    (hφ₁_range : ∀ s, φ₁ s ∈ Icc 0 1)
    (hzero₁ : ∀ s ≤ -L₁, φ₁ s = 0)
    (hone₁ : ∀ s, L₁ ≤ s → φ₁ s = 1)
    (hA₁c : IsCompact (closure A₁))
    (hA₂ : IsOpen A₂) (hB₂ : IsOpen B₂)
    (hdisj₂ : Disjoint A₂ B₂) (hcover₂ : A₂ ∪ B₂ = N₂.central_sphereᶜ)
    (hneg₂ : N₂.region (-N₂.epsilon⁻¹) 0 ⊆ A₂)
    (hpos₂ : N₂.region 0 N₂.epsilon⁻¹ ⊆ B₂)
    {L₂ : ℝ} (hL₂ : 0 < L₂) (hLe₂ : L₂ < N₂.epsilon⁻¹)
    (hφ₂ : ContDiff ℝ ∞ φ₂)
    (hφ₂_range : ∀ s, φ₂ s ∈ Icc 0 1)
    (hzero₂ : ∀ s ≤ -L₂, φ₂ s = 0)
    (hone₂ : ∀ s, L₂ ≤ s → φ₂ s = 1)
    (hA₂c : IsCompact (closure A₂))
    (hneck : Disjoint N₁.carrier N₂.carrier)
    (hinner : N₁.carrier ⊆ A₂)
    (houter : Disjoint A₁ N₂.carrier)
    (hnest : A₁ ⊆ A₂) :
    0 ≤ ∫ x, mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient (fun y => N₁.axialTransition A₁ φ₁ y -
        N₂.axialTransition A₂ φ₂ y) x) ∂g.volumeMeasure := by
  have hT₁ := N₁.contMDiff_axialTransition hA₁ hB₁ hdisj₁ hcover₁
    hneg₁ hpos₁ hL₁ hLe₁
      hφ₁ hzero₁ hone₁
  have hT₂ := N₂.contMDiff_axialTransition hA₂ hB₂ hdisj₂ hcover₂
    hneg₂ hpos₂ hL₂ hLe₂
      hφ₂ hzero₂ hone₂
  have hc₁ := N₁.hasCompactSupport_one_sub_axialTransition hA₁c hdisj₁
    hcover₁ hneg₁ hL₁ hLe₁ hone₁
  have hc₂ := N₂.hasCompactSupport_one_sub_axialTransition hA₂c hdisj₂
    hcover₂ hneg₂ hL₂ hLe₂ hone₂
  have hcompact := N₁.hasCompactSupport_axialTransition_sub N₂ hc₁ hc₂
  have hnonneg : ∀ x, 0 ≤ N₁.axialTransition A₁ φ₁ x -
      N₂.axialTransition A₂ φ₂ x := fun x =>
    N₁.axialTransition_sub_nonneg N₂
      hφ₁_range hφ₂_range
      hneck hinner houter hnest x
  exact (g.ray_busemann_integral_differential_nonneg D (by norm_num) hc
    hm hdist hray
    (fun y => N₁.axialTransition A₁ φ₁ y - N₂.axialTransition A₂ φ₂ y)
    (hT₁.sub hT₂) hcompact hnonneg).2

end PoincareConjecture.EpsilonNeck
