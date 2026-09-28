import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Separation.Ordering
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Directional.Busemann
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.IntegralBounds.Directional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.IntegralBounds.ScaleComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.WeakComparison.Oriented












noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff
open PoincareConjecture Poincare.Riemannian.Soul

universe u



theorem PoincareConjecture.RiemannianMetric.exists_universal_neck_scale_lower_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 2 ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [ConnectedSpace M] [Nonempty M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M],
      ∀ (g : PoincareConjecture.RiemannianMetric 3 M) (D : PoincareConjecture.LeviCivitaData g),
        PoincareConjecture.MetricComplete g → D.StrictlyPositiveSectionalCurvature →
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ N : PoincareConjecture.EpsilonNeck g, N.epsilon = ε → ρ ≤ N.scale := by
  classical
  obtain ⟨εg, hεg, hgrad⟩ := EpsilonNeck.exists_outward_busemann_gradient_threshold.{u}
  refine ⟨min εg neckSeparationThreshold, lt_min hεg neckSeparationThreshold_pos,
    (min_le_right _ _).trans_lt neckSeparationThreshold_lt_half, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D hc hpos ε hε hεbound
  by_cases hcompact : CompactSpace M
  · let : CompactSpace M := hcompact
    obtain ⟨ρ, hρ, hscale⟩ := EpsilonNeck.exists_scale_lower_bound_of_compactSpace D
    exact ⟨ρ, hρ, fun N _ => hscale N⟩
  · let : NoncompactSpace M := not_compactSpace_iff.mp hcompact
    obtain ⟨P⟩ := g.exists_pointSoulData_of_strictlyPositiveSectionalCurvature D hc hpos
    let : MetricSpace M := g.toMetricSpace
    have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
    let : ProperSpace M := g.properSpace_of_complete hc hdist
    obtain ⟨ray, hray, _, _⟩ := exists_ray_in_closed_set (K := (univ : Set M))
      isClosed_univ (noncompact_univ M) (p := P.center) (by
        intro q _
        obtain ⟨curve, h0, h1, hmin, _⟩ :=
          g.exists_smooth_metric_segment_of_complete hc hdist P.center q
        exact ⟨curve, h0, h1, hmin, fun _ _ => mem_univ _⟩)
    have hRic : D.NonnegativeRicciCurvature := by
      intro x v
      exact Finset.sum_nonneg fun i _ => (hpos.nonnegative D) x v (g.orthonormalBasis x i)
    by_contra hsmall
    obtain ⟨N₁, hε₁, _⟩ : ∃ N : EpsilonNeck g, N.epsilon = ε ∧ N.scale < 1 := by
      by_contra! hnone
      exact hsmall ⟨1, zero_lt_one, hnone⟩
    have hsmall₁ : ¬ ∃ ρ : ℝ, 0 < ρ ∧
        ∀ N : EpsilonNeck g, N.epsilon = N₁.epsilon → ρ ≤ N.scale := by
      simpa only [hε₁] using hsmall
    have hN₁s : N₁.epsilon ≤ neckSeparationThreshold := by
      rw [hε₁]
      exact hεbound.trans (min_le_right _ _)
    have hN₁g : N₁.epsilon ≤ εg := by
      rw [hε₁]
      exact hεbound.trans (min_le_left _ _)
    obtain ⟨A₁, B₁, hA₁, hB₁, _, _, hdisj₁, hcover₁, hfA₁, _,
        hcompact₁, _, _, hhalf₁, houter⟩ :=
      P.exists_arbitrarily_small_outer_neck_regions D hc N₁ hN₁s hsmall₁
    obtain ⟨N₂, A₂, B₂, _, hscale₂, _, hA₂, hB₂, _, _, hdisj₂, hcover₂,
        _, _, hcompact₂, _, _, hhalf₂, hnecks, _, hinner, houterdisj, hnest⟩ :=
      houter (N₁.scale / 8) (div_pos N₁.scale_pos (by norm_num))
    have hL₁ : (1 : ℝ) < N₁.epsilon⁻¹ :=
      (one_lt_inv₀ N₁.epsilon_pos).mpr (by linarith [N₁.epsilon_lt_half])
    have hL₂ : (1 : ℝ) < N₂.epsilon⁻¹ :=
      (one_lt_inv₀ N₂.epsilon_pos).mpr (by linarith [N₂.epsilon_lt_half])
    obtain ⟨ψ₁, ψ₂, hkind₁, hkind₂, _, _, _, _, _, _, _, _, hI₁, hI₂, hcompare⟩ :=
      EpsilonNeck.exists_outward_profiles_busemann_flux_comparison D hc hdist hRic hray
        N₁ N₂ hA₁ hB₁ hdisj₁ hcover₁ hhalf₁ hcompact₁ (by norm_num) hL₁
        (contDiff_axialTransitionProfile 1) (axialTransitionProfile_mem_Icc 1)
        (fun _ hs => axialTransitionProfile_zero (by norm_num) hs)
        (fun _ hs => axialTransitionProfile_one (by norm_num) hs)
        hA₂ hB₂ hdisj₂ hcover₂ hhalf₂ hcompact₂ (by norm_num) hL₂
        (contDiff_axialTransitionProfile 1) (axialTransitionProfile_mem_Icc 1)
        (fun _ hs => axialTransitionProfile_zero (by norm_num) hs)
        (fun _ hs => axialTransitionProfile_one (by norm_num) hs)
        hnecks hinner houterdisj hnest
    obtain ⟨σ, hprofile, hsign⟩ : ∃ σ : ℝ,
        ((σ = -1 ∧ ψ₁ = axialTransitionProfile 1) ∨
          (σ = 1 ∧ ψ₁ = fun s => 1 - axialTransitionProfile 1 s)) ∧
        ((σ = -1 ∧ N₁.region (-N₁.epsilon⁻¹) 0 ⊆ A₁) ∨
          (σ = 1 ∧ N₁.region 0 N₁.epsilon⁻¹ ⊆ A₁)) := by
      rcases hkind₁ with ⟨hneg, _, hψ⟩ | ⟨_, hpos, hψ⟩
      · exact ⟨-1, Or.inl ⟨rfl, hψ⟩, Or.inl ⟨rfl, hneg⟩⟩
      · exact ⟨1, Or.inr ⟨rfl, hψ⟩, Or.inr ⟨rfl, hpos⟩⟩
    have hclose := hgrad N₁ D hc hdist hray hN₁g hA₁ hfA₁ hcompact₁ hhalf₁ hsign
    have hlower := N₁.integral_neg_outward_axialTransition_flux_lower_of_gradient_distance
      D A₁ (by norm_num) hL₁.le hprofile hclose hI₁.integrableOn
    have hψ₂ : ψ₂ = axialTransitionProfile 1 ∨
        ψ₂ = fun s => 1 - axialTransitionProfile 1 s :=
      hkind₂.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
    have hratio := N₁.scale_div_eight_le_of_outward_flux_comparison N₂ D hc hdist hray
      A₁ A₂ ψ₁ (by norm_num) hL₂.le hψ₂ hI₂.integrableOn hlower hcompare
    exact (not_lt_of_ge hratio) hscale₂
