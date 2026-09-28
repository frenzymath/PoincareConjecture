import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Terminal

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.AncientCompactness

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y]

theorem exists_smooth_terminal_limit_same_sequence_of_eventually
    {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ) (f : ℕ → ℝ × X → Y)
    (hf : ∀ᶠ k : ℕ in atTop, ContDiffOn ℝ ∞ (f k) (Iic 0 ×ˢ closedBall x₀ ρ))
    (g : (m : ℕ) → ℝ × X → (ℝ × X) [×m]→L[ℝ] Y)
    (hinterior : ∀ m K, IsCompact K → K ⊆ Iio 0 ×ˢ closedBall x₀ ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f k) (Iic 0 ×ˢ closedBall x₀ ρ))
        (g m) atTop K)
    (hbound : ∀ K : Set (ℝ × X), IsCompact K →
      K ⊆ Iic 0 ×ˢ closedBall x₀ ρ → ∀ m : ℕ,
        ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
          ‖iteratedFDerivWithin ℝ m (f k) (Iic 0 ×ˢ closedBall x₀ ρ) z‖ ≤ B) :
    ∃ F : ℝ × X → Y, ContDiffOn ℝ ∞ F (Iic 0 ×ˢ closedBall x₀ ρ) ∧
      ∀ m K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall x₀ ρ →
        TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m (f k) (Iic 0 ×ˢ closedBall x₀ ρ))
          (iteratedFDerivWithin ℝ m F (Iic 0 ×ˢ closedBall x₀ ρ)) atTop K := by
  let Ω : Set (ℝ × X) := Iic 0 ×ˢ closedBall x₀ ρ
  have hclosed : IsClosed Ω := isClosed_Iic.prod isClosed_closedBall
  have hconvex : Convex ℝ Ω := (convex_Iic 0).prod (convex_closedBall x₀ ρ)
  have hne : (interior Ω).Nonempty := by
    rw [show Ω = Iic 0 ×ˢ closedBall x₀ ρ from rfl,
      interior_prod_eq, interior_Iic, interior_closedBall x₀ hρ.ne']
    exact ⟨(-1, x₀), by simp [hρ]⟩
  have hunique := uniqueDiffOn_convex hconvex hne
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  let f' := fun k => f (max k N)
  have hf' (k : ℕ) : ContDiffOn ℝ ∞ (f' k) Ω := hN _ (le_max_right k N)
  have heq : ∀ᶠ k : ℕ in atTop, f' k = f k :=
    (eventually_ge_atTop N).mono fun k hk => congrArg f (max_eq_left hk)
  have hbound' (K : Set (ℝ × X)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k z, z ∈ K → ‖iteratedFDerivWithin ℝ m (f' k) Ω z‖ ≤ B := by
    obtain ⟨B, hB, hevent⟩ := hbound K hK hKΩ m
    obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
    have hfinite (k : Fin M) : ∃ C : ℝ, ∀ z ∈ K,
        ‖iteratedFDerivWithin ℝ m (f' k) Ω z‖ ≤ C :=
      hK.exists_bound_of_continuousOn
        (((hf' k).continuousOn_iteratedFDerivWithin
          (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)) hunique).mono hKΩ)
    choose C hC using hfinite
    let D := ∑ k : Fin M, max (C k) 0
    have hD : 0 ≤ D := Finset.sum_nonneg fun k _ => le_max_right (C k) 0
    refine ⟨max B D, le_max_of_le_left hB, ?_⟩
    intro k z hz
    by_cases hk : M ≤ k
    · exact (hM (max k N) (hk.trans (le_max_left k N)) z hz).trans (le_max_left B D)
    · have hkM : k < M := lt_of_not_ge hk
      have hCD : C ⟨k, hkM⟩ ≤ D :=
        (le_max_left (C ⟨k, hkM⟩) 0).trans
          (Finset.single_le_sum (fun i _ => le_max_right (C i) 0)
            (Finset.mem_univ (⟨k, hkM⟩ : Fin M)))
      exact (hC ⟨k, hkM⟩ z hz).trans (hCD.trans (le_max_right B D))
  obtain ⟨σ, hσ, F, hF, hjets⟩ :=
    Poincare.AncientVolume.exists_smooth_subsequence_on_closed_convex
      hclosed hconvex hne f' hf' hbound'
  have hsame (m : ℕ) : EqOn (g m) (iteratedFDerivWithin ℝ m F Ω)
      (Iio 0 ×ˢ closedBall x₀ ρ) := by
    intro z hz
    have hinside := hinterior m {z} isCompact_singleton (singleton_subset_iff.mpr hz)
    have hinside' : TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f' k) Ω) (g m) atTop {z} :=
      hinside.congr (heq.mono fun k hk y _ => by rw [hk])
    apply tendsto_nhds_unique
      ((hinside'.tendsto_at (mem_singleton z)).comp hσ.tendsto_atTop)
    exact (hjets m {z} isCompact_singleton
      (singleton_subset_iff.mpr ⟨le_of_lt (show z.1 < 0 from hz.1), hz.2⟩)).tendsto_at
        (mem_singleton z)
  refine ⟨F, hF, ?_⟩
  intro m K hK hKΩ
  apply tendstoUniformlyOn_past_of_time_lipschitz
    (U := closedBall x₀ ρ) ?_ ?_ ?_ hK hKΩ
  · intro A hA hAU
    exact (hinterior m A hA hAU).congr_right fun z hz => hsame m (hAU hz)
  · intro x hx
    have hc := hF.continuousOn_iteratedFDerivWithin
      (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)) hunique
    exact hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht.2, hx⟩)
  · intro V hV hVU
    obtain ⟨B, hB, hBbound⟩ := hbound (Icc (-1) 0 ×ˢ V)
      (isCompact_Icc.prod hV) (prod_mono (fun _ ht => ht.2) hVU) (m + 1)
    refine ⟨B, hB, ?_⟩
    filter_upwards [hf, hBbound] with k hk hBk x hx s hs t ht
    let Q : Set (ℝ × X) := Icc (-1) 0 ×ˢ {x}
    have hQ : Convex ℝ Q := (convex_Icc (-1) 0).prod (convex_singleton x)
    have hQΩ : Q ⊆ Ω := by
      rintro ⟨u, y⟩ ⟨hu, hy⟩
      rcases mem_singleton_iff.mp hy with rfl
      exact ⟨hu.2, hVU hx⟩
    have hdiff := hk.differentiableOn_iteratedFDerivWithin
      (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m) hunique
    have hnorm : ‖iteratedFDerivWithin ℝ m (f k) Ω (s, x) -
        iteratedFDerivWithin ℝ m (f k) Ω (t, x)‖ ≤ B * ‖(s, x) - (t, x)‖ := by
      apply hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => (hdiff z (hQΩ hz)).hasFDerivWithinAt.mono hQΩ)
        (fun z hz => ?_) ⟨ht, mem_singleton x⟩ ⟨hs, mem_singleton x⟩
      rw [norm_fderivWithin_iteratedFDerivWithin]
      exact hBk z ⟨hz.1, (mem_singleton_iff.mp hz.2) ▸ hx⟩
    simpa only [dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def,
      norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg (s - t))] using hnorm

end PoincareConjecture.AncientCompactness
