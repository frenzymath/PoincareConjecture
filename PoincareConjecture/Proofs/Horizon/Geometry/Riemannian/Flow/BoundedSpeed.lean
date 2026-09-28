import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Global
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurvePasting








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_smooth_globalFlow_of_bounded_speed
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, g.tangentNorm x (X x) ≤ C) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.2⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ univ) := (hX.comp contMDiff_snd).contMDiffOn
  have hconf (s : ℝ) (_ : s ∈ (univ : Set ℝ)) (x : M) (a b : ℝ)
      (hsab : s ∈ Icc a b) (_ : Icc a b ⊆ (univ : Set ℝ)) :
      ∃ K : Set M, IsCompact K ∧ ∀ (I : Set ℝ), IsOpen I → Convex ℝ I → s ∈ I →
        ∀ (γ : ℝ → M), γ s = x → ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I →
          (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) →
          ∀ t ∈ I ∩ Icc a b, γ t ∈ K := by
    refine ⟨{y | g.edist x y ≤ ENNReal.ofReal (C * (b - a))},
      g.isCompact_closedBall_of_metricComplete hc x _, ?_⟩
    intro I hI hconv hsI γ hinit hγ hODE t ht
    have hspeed (u : ℝ) (hu : u ∈ I) :
        g.tangentNorm (γ u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) ≤ C := by
      rw [(hODE u hu).mfderiv]
      change g.tangentNorm (γ u) ((1 : ℝ) • X (γ u)) ≤ C
      simpa only [one_smul] using hbound (γ u)
    have hsub : uIcc s t ⊆ I := hconv.ordConnected.uIcc_subset hsI ht.1
    change g.edist x (γ t) ≤ _
    rw [← hinit]
    rcases le_total s t with hst | hts
    · have hd := g.edist_le_of_speed_le_on_Icc hI hγ hst
        (by simpa only [uIcc_of_le hst] using hsub)
        (fun u hu => hspeed u (hsub (by simpa only [uIcc_of_le hst] using hu)))
      exact hd.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (by linarith [hsab.1, ht.2.2]) hC))
    · have hd := g.edist_le_of_speed_le_on_Icc hI hγ hts
        (by simpa only [uIcc_of_ge hts] using hsub)
        (fun u hu => hspeed u (hsub (by simpa only [uIcc_of_ge hts] using hu)))
      rw [show g.edist (γ t) (γ s) = g.edist (γ s) (γ t) from
        Manifold.riemannianEDist_comm] at hd
      exact hd.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (by linarith [hsab.2, ht.2.1]) hC))
  obtain ⟨E, hi, hs, hODE, _, _⟩ :=
    Poincare.Manifold.exists_smooth_global_timeDependentFlow_of_compact_confinement
      (X := fun _ => X) isOpen_univ convex_univ hsmooth hconf
  let Φ : ℝ → M → M := E 0
  have hinit : ∀ x, Φ 0 x = x := hi 0 (mem_univ 0)
  have hcurve : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X :=
    fun x t => hODE 0 (mem_univ 0) x t (mem_univ t)
  refine ⟨Φ, hinit, hcurve, ?_, ?_⟩
  · intro s t x
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
      (hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
      ((hcurve x).comp_add t) (hcurve (Φ t x)) (by
        simp only [Function.comp_apply, zero_add, hinit])
    exact congrFun he s
  · apply contMDiffOn_univ.mp
    simpa only [univ_prod_univ, Φ, Function.uncurry] using! hs 0 (mem_univ 0)

end PoincareConjecture.RiemannianMetric
