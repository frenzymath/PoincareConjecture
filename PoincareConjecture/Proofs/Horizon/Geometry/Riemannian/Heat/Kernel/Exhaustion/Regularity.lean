import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.CoordinateKernel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.SpacetimeJets
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Uniqueness









set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n d : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin d)

theorem contDiffOn_coordinateExhaustionKernel [PreconnectedSpace M]
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (hei₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁.symm e₁.target)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    (hei₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂.symm e₂.target) :
    ContDiffOn ℝ ∞
      (coordinateExhaustionKernel D S T X Y e₁ e₂)
      (coordinateKernelDomain T X Y e₁ e₂) := by
  apply Poincare.Analysis.Calculus.contDiffOn_of_locally_eventually_smooth
  · intro z hz
    simpa only [coordinateHeatKernel, coordinateExhaustionKernel] using
      (tendsto_coordinateHeatKernel D hc hk hRic S hΩmono hcover T X Y e₁ e₂ hz)
  · exact locally_eventually_smooth_coordinateHeatKernel D S hΩmono hcover T X Y
      e₁ e₂ he₁ he₂
  · exact locallyEventuallyBoundedDerivatives_coordinateHeatKernel D hc hk hRic S
      hΩmono hcover T X Y e₁ e₂ he₁ hei₁ he₂ hei₂




theorem tendsto_iteratedFDeriv_coordinateExhaustionKernel [PreconnectedSpace M]
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (hei₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁.symm e₁.target)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    (hei₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂.symm e₂.target)
    (m : ℕ) {z : F} (hz : z ∈ coordinateKernelDomain T X Y e₁ e₂) :
    Tendsto
      (fun q => iteratedFDeriv ℝ m
        (coordinateHeatKernel D (S q) T X Y e₁ e₂) z) atTop
      (𝓝 (iteratedFDeriv ℝ m
        (coordinateExhaustionKernel D S T X Y e₁ e₂) z)) := by
  apply Poincare.Analysis.Calculus.tendsto_iteratedFDeriv_of_locally_eventually_smooth
    (m := m) (x := z)
  · intro w hw
    exact Dirichlet.tendsto_coordinateHeatKernel D hc hk hRic S hΩmono hcover
      T X Y e₁ e₂ hw
  · exact Dirichlet.locally_eventually_smooth_coordinateHeatKernel D S hΩmono
      hcover T X Y e₁ e₂ he₁ he₂
  · exact Dirichlet.locallyEventuallyBoundedDerivatives_coordinateHeatKernel D hc hk
      hRic S hΩmono hcover T X Y e₁ e₂ he₁ hei₁ he₂ hei₂
  · exact hz

theorem contDiffOn_chartExhaustionKernel [PreconnectedSpace M]
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (hei₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁.symm e₁.target)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    (hei₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂.symm e₂.target) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × E) × E => dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) z.1.1 (e₁ z.1.2) (e₂ z.2))
      ((Ioi 0 ×ˢ e₁.source) ×ˢ e₂.source) := by
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ ((ℝ × E) × E))) ≃L[ℝ]
      ((ℝ × E) × E) := (toEuclidean).symm
  let T := (ContinuousLinearMap.fst ℝ ℝ E).comp
    ((ContinuousLinearMap.fst ℝ (ℝ × E) E).comp L.toContinuousLinearMap)
  let X := (ContinuousLinearMap.snd ℝ ℝ E).comp
    ((ContinuousLinearMap.fst ℝ (ℝ × E) E).comp L.toContinuousLinearMap)
  let Y := (ContinuousLinearMap.snd ℝ (ℝ × E) E).comp L.toContinuousLinearMap
  have hs := contDiffOn_coordinateExhaustionKernel D hc hk hRic S hΩmono hcover
    T X Y e₁ e₂ he₁ hei₁ he₂ hei₂
  intro z hz
  have hz' : L.symm z ∈ coordinateKernelDomain T X Y e₁ e₂ := by
    simpa [coordinateKernelDomain, T, X, Y] using And.intro hz.1.1 ⟨hz.1.2, hz.2⟩
  have h := (hs.contDiffAt
    ((isOpen_coordinateKernelDomain T X Y e₁ e₂).mem_nhds hz')).comp z
      L.symm.contDiff.contDiffAt
  have h' : ContDiffWithinAt ℝ ∞
      (coordinateExhaustionKernel D S T X Y e₁ e₂ ∘ L.symm)
      (L.symm ⁻¹' coordinateKernelDomain T X Y e₁ e₂) z := h.contDiffWithinAt
  convert h' using 1
  · simp [coordinateExhaustionKernel, T, X, Y, Function.comp_def,
      L.apply_symm_apply]
  · ext a
    simp only [coordinateKernelDomain, Set.mem_setOf_eq, Set.mem_preimage,
      T, X, Y, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ]
    have hLa : L.toContinuousLinearMap (L.symm a) = a := L.apply_symm_apply a
    rw [hLa]
    constructor
    · rintro ⟨⟨ht, hx⟩, hy⟩
      exact ⟨ht, hx, hy⟩
    · rintro ⟨ht, hx, hy⟩
      exact ⟨⟨ht, hx⟩, hy⟩


theorem contMDiffOn_dirichletExhaustionKernel [PreconnectedSpace M]
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ) :
    ContMDiffOn ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × M) × M => dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) p.1.1 p.1.2 p.2)
      ((Ioi 0 ×ˢ univ) ×ˢ univ) := by
  intro p hp
  let c₁ := chartAt E p.1.2
  let c₂ := chartAt E p.2
  have hx : p.1.2 ∈ c₁.source := mem_chart_source E p.1.2
  have hy : p.2 ∈ c₂.source := mem_chart_source E p.2
  let z : (ℝ × E) × E := ((p.1.1, c₁ p.1.2), c₂ p.2)
  have hz : z ∈ ((Ioi 0 ×ˢ c₁.target) ×ˢ c₂.target) :=
    ⟨⟨hp.1.1, c₁.map_source hx⟩, c₂.map_source hy⟩
  have hs := (contDiffOn_chartExhaustionKernel D hc hk hRic S hΩmono hcover
    c₁.symm c₂.symm contMDiffOn_chart_symm contMDiffOn_chart
    contMDiffOn_chart_symm contMDiffOn_chart).contDiffAt
      (((isOpen_Ioi.prod c₁.open_target).prod c₂.open_target).mem_nhds hz)
  have hxsm : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c₁ p.1.2 :=
    (contMDiffOn_chart (I := 𝓡 n) (H := E) (x := p.1.2)).contMDiffAt
    (c₁.open_source.mem_nhds hx)
  have hysm : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c₂ p.2 :=
    (contMDiffOn_chart (I := 𝓡 n) (H := E) (x := p.2)).contMDiffAt
    (c₂.open_source.mem_nhds hy)
  have hφ : ContMDiffAt ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n))
      𝓘(ℝ, (ℝ × E) × E) ∞
      (fun q : (ℝ × M) × M => ((q.1.1, c₁ q.1.2), c₂ q.2)) p :=
    (contMDiffAt_fst.fst.prodMk_space (hxsm.comp p contMDiffAt_fst.snd)).prodMk_space
      (hysm.comp p contMDiffAt_snd)
  have h := hs.contMDiffAt.comp p hφ
  apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(continuous_fst.snd.tendsto p) (c₁.open_source.mem_nhds hx),
    (continuous_snd.tendsto p) (c₂.open_source.mem_nhds hy)] with q hqx hqy
  simp only [Function.comp_def, c₁.left_inv hqx, c₂.left_inv hqy]

end PoincareConjecture.LeviCivitaData.Dirichlet
