import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.Oriented
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Decomposition

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology
open Poincare.Riemannian.Soul

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}

private theorem integrable_busemann_flux_of_compact_complement
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hm : D.NonnegativeRicciCurvature) {ray : ℝ → M} (hray : IsRay ray)
    {T : M → ℝ} (hT : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ T)
    (hcompact : HasCompactSupport (fun x => 1 - T x)) (hTle : ∀ x, T x ≤ 1) :
    Integrable (fun x => mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient T x)) g.volumeMeasure := by
  obtain ⟨hI, _⟩ := g.ray_busemann_integral_differential_nonneg D (by norm_num)
    hc hm hdist hray (fun x => 1 - T x) (contMDiff_const.sub hT) hcompact
    (fun x => sub_nonneg.mpr (hTle x))
  have hgrad (x : M) : D.gradient (fun y => 1 - T y) x = -D.gradient T x := by
    apply (g.inner_isInvertible x).injective
    ext v
    rw [D.inner_gradient, mvfderiv_fun_sub mdifferentiableAt_const
      ((hT x).mdifferentiableAt (by simp))]
    simp only [mvfderiv_const, zero_sub, map_neg]
    change -mvfderiv (𝓡 3) T x v = -g.inner x (D.gradient T x) v
    rw [D.inner_gradient]
  apply hI.neg.congr
  filter_upwards [] with x
  change -mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient (fun y => 1 - T y) x) = mvfderiv (𝓡 3) (busemann ray) x (D.gradient T x)
  rw [hgrad]
  simp

theorem exists_outward_axialTransition_flux
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hm : D.NonnegativeRicciCurvature) {ray : ℝ → M} (hray : IsRay ray)
    (N : EpsilonNeck g) {A B : Set M}
    (hA : IsOpen A) (hB : IsOpen B) (hdisj : Disjoint A B)
    (hcover : A ∪ B = N.central_sphereᶜ)
    (hhalf :
      (N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
      (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A))
    (hAc : IsCompact (closure A))
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hφ : ContDiff ℝ ∞ φ) (hrange : ∀ s, φ s ∈ Icc 0 1)
    (hzero : ∀ s ≤ -L, φ s = 0) (hone : ∀ s, L ≤ s → φ s = 1) :
    ∃ ψ : ℝ → ℝ,
      ((N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B ∧ ψ = φ) ∨
        (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A ∧
          ψ = fun s => 1 - φ s)) ∧
      ContDiff ℝ ∞ ψ ∧ (∀ s, ψ s ∈ Icc 0 1) ∧
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (N.axialTransition A ψ) ∧
      HasCompactSupport (fun x => 1 - N.axialTransition A ψ x) ∧
      (∀ x ∉ N.carrier, D.gradient (N.axialTransition A ψ) x = 0) ∧
      Integrable (fun x => mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient (N.axialTransition A ψ) x)) g.volumeMeasure := by
  obtain ⟨ψ, hkind, hψ, hψrange, hT, hcompact, hlocal⟩ :=
    N.exists_outward_axialTransition hA hB hdisj hcover hhalf hAc hL hLe
      hφ hrange hzero hone
  refine ⟨ψ, hkind, hψ, hψrange, hT, hcompact, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, he⟩ := hlocal x hx
    unfold LeviCivitaData.gradient mvfderiv
    rw [he.mfderiv_eq, he.eq_of_nhds]
    simp
  · exact integrable_busemann_flux_of_compact_complement D hc hdist hm hray hT hcompact
      (fun x => (N.axialTransition_mem_Icc hψrange x).2)

theorem exists_outward_profiles_busemann_flux_comparison
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hm : D.NonnegativeRicciCurvature) {ray : ℝ → M} (hray : IsRay ray)
    (N₁ N₂ : EpsilonNeck g) {A₁ B₁ A₂ B₂ : Set M} {φ₁ φ₂ : ℝ → ℝ}
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁)
    (hdisj₁ : Disjoint A₁ B₁) (hcover₁ : A₁ ∪ B₁ = N₁.central_sphereᶜ)
    (hhalf₁ :
      (N₁.region (-N₁.epsilon⁻¹) 0 ⊆ A₁ ∧ N₁.region 0 N₁.epsilon⁻¹ ⊆ B₁) ∨
      (N₁.region (-N₁.epsilon⁻¹) 0 ⊆ B₁ ∧ N₁.region 0 N₁.epsilon⁻¹ ⊆ A₁))
    (hAc₁ : IsCompact (closure A₁))
    {L₁ : ℝ} (hL₁ : 0 < L₁) (hLe₁ : L₁ < N₁.epsilon⁻¹)
    (hφ₁ : ContDiff ℝ ∞ φ₁) (hrange₁ : ∀ s, φ₁ s ∈ Icc 0 1)
    (hzero₁ : ∀ s ≤ -L₁, φ₁ s = 0) (hone₁ : ∀ s, L₁ ≤ s → φ₁ s = 1)
    (hA₂ : IsOpen A₂) (hB₂ : IsOpen B₂)
    (hdisj₂ : Disjoint A₂ B₂) (hcover₂ : A₂ ∪ B₂ = N₂.central_sphereᶜ)
    (hhalf₂ :
      (N₂.region (-N₂.epsilon⁻¹) 0 ⊆ A₂ ∧ N₂.region 0 N₂.epsilon⁻¹ ⊆ B₂) ∨
      (N₂.region (-N₂.epsilon⁻¹) 0 ⊆ B₂ ∧ N₂.region 0 N₂.epsilon⁻¹ ⊆ A₂))
    (hAc₂ : IsCompact (closure A₂))
    {L₂ : ℝ} (hL₂ : 0 < L₂) (hLe₂ : L₂ < N₂.epsilon⁻¹)
    (hφ₂ : ContDiff ℝ ∞ φ₂) (hrange₂ : ∀ s, φ₂ s ∈ Icc 0 1)
    (hzero₂ : ∀ s ≤ -L₂, φ₂ s = 0) (hone₂ : ∀ s, L₂ ≤ s → φ₂ s = 1)
    (hneck : Disjoint N₁.carrier N₂.carrier)
    (hinner : N₁.carrier ⊆ A₂) (houter : Disjoint A₁ N₂.carrier) (hnest : A₁ ⊆ A₂) :
    ∃ ψ₁ ψ₂ : ℝ → ℝ,
      ((N₁.region (-N₁.epsilon⁻¹) 0 ⊆ A₁ ∧ N₁.region 0 N₁.epsilon⁻¹ ⊆ B₁ ∧ ψ₁ = φ₁) ∨
        (N₁.region (-N₁.epsilon⁻¹) 0 ⊆ B₁ ∧ N₁.region 0 N₁.epsilon⁻¹ ⊆ A₁ ∧
          ψ₁ = fun s => 1 - φ₁ s)) ∧
      ((N₂.region (-N₂.epsilon⁻¹) 0 ⊆ A₂ ∧ N₂.region 0 N₂.epsilon⁻¹ ⊆ B₂ ∧ ψ₂ = φ₂) ∨
        (N₂.region (-N₂.epsilon⁻¹) 0 ⊆ B₂ ∧ N₂.region 0 N₂.epsilon⁻¹ ⊆ A₂ ∧
          ψ₂ = fun s => 1 - φ₂ s)) ∧
      ContDiff ℝ ∞ ψ₁ ∧ ContDiff ℝ ∞ ψ₂ ∧
      (∀ s, ψ₁ s ∈ Icc 0 1) ∧ (∀ s, ψ₂ s ∈ Icc 0 1) ∧
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (N₁.axialTransition A₁ ψ₁) ∧
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (N₂.axialTransition A₂ ψ₂) ∧
      (∀ x ∉ N₁.carrier, D.gradient (N₁.axialTransition A₁ ψ₁) x = 0) ∧
      (∀ x ∉ N₂.carrier, D.gradient (N₂.axialTransition A₂ ψ₂) x = 0) ∧
      Integrable (fun x => mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient (N₁.axialTransition A₁ ψ₁) x)) g.volumeMeasure ∧
      Integrable (fun x => mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient (N₂.axialTransition A₂ ψ₂) x)) g.volumeMeasure ∧
      0 ≤ (∫ x in N₁.carrier, mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient (N₁.axialTransition A₁ ψ₁) x) ∂g.volumeMeasure) -
        (∫ x in N₂.carrier, mvfderiv (𝓡 3) (busemann ray) x
          (D.gradient (N₂.axialTransition A₂ ψ₂) x) ∂g.volumeMeasure) := by
  obtain ⟨ψ₁, hkind₁, hψ₁, hψrange₁, hT₁, hcompact₁, hgrad₁, hI₁⟩ :=
    exists_outward_axialTransition_flux D hc hdist hm hray N₁ hA₁ hB₁ hdisj₁ hcover₁
      hhalf₁ hAc₁ hL₁ hLe₁ hφ₁ hrange₁ hzero₁ hone₁
  obtain ⟨ψ₂, hkind₂, hψ₂, hψrange₂, hT₂, hcompact₂, hgrad₂, hI₂⟩ :=
    exists_outward_axialTransition_flux D hc hdist hm hray N₂ hA₂ hB₂ hdisj₂ hcover₂
      hhalf₂ hAc₂ hL₂ hLe₂ hφ₂ hrange₂ hzero₂ hone₂
  refine ⟨ψ₁, ψ₂, hkind₁, hkind₂, hψ₁, hψ₂, hψrange₁, hψrange₂,
    hT₁, hT₂, hgrad₁, hgrad₂, hI₁, hI₂, ?_⟩
  have hcompact := N₁.hasCompactSupport_axialTransition_sub N₂ hcompact₁ hcompact₂
  have hnonneg : ∀ x, 0 ≤ N₁.axialTransition A₁ ψ₁ x - N₂.axialTransition A₂ ψ₂ x :=
    N₁.axialTransition_sub_nonneg N₂ hψrange₁ hψrange₂ hneck hinner houter hnest
  have hweak := (g.ray_busemann_integral_differential_nonneg D (by norm_num) hc hm
    hdist hray (fun x => N₁.axialTransition A₁ ψ₁ x - N₂.axialTransition A₂ ψ₂ x)
    (hT₁.sub hT₂) hcompact hnonneg).2
  rw [integral_busemann_transition_difference_eq_restricted D N₁ N₂
    (N₁.axialTransition A₁ ψ₁) (N₂.axialTransition A₂ ψ₂)
    hT₁ hT₂ hgrad₁ hgrad₂ hneck hI₁ hI₂] at hweak
  exact hweak

end PoincareConjecture.EpsilonNeck
