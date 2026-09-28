import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.TerminalJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.ClosedCompactness

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.AncientCompactness

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y]

theorem exists_smooth_terminal_limit_same_sequence
    {ρ : ℝ} (hρ : 0 < ρ) (f : ℕ → ℝ × X → Y)
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) (Iic 0 ×ˢ closedBall 0 ρ))
    (g : (m : ℕ) → ℝ × X → (ℝ × X) [×m]→L[ℝ] Y)
    (hinterior : ∀ m K, IsCompact K → K ⊆ Iio 0 ×ˢ closedBall (0 : X) ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f k) (Iic 0 ×ˢ closedBall 0 ρ))
        (g m) atTop K)
    (hbound : ∀ K : Set (ℝ × X), IsCompact K →
      K ⊆ Iic 0 ×ˢ closedBall (0 : X) ρ → ∀ m : ℕ,
        ∃ B : ℝ, 0 ≤ B ∧ ∀ k z, z ∈ K →
          ‖iteratedFDerivWithin ℝ m (f k) (Iic 0 ×ˢ closedBall 0 ρ) z‖ ≤ B) :
    ∃ F : ℝ × X → Y, ContDiffOn ℝ ∞ F (Iic 0 ×ˢ closedBall 0 ρ) ∧
      ∀ m K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall (0 : X) ρ →
        TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m (f k) (Iic 0 ×ˢ closedBall 0 ρ))
          (iteratedFDerivWithin ℝ m F (Iic 0 ×ˢ closedBall 0 ρ)) atTop K := by
  let Ω : Set (ℝ × X) := Iic 0 ×ˢ closedBall 0 ρ
  have hclosed : IsClosed Ω := isClosed_Iic.prod isClosed_closedBall
  have hconvex : Convex ℝ Ω := (convex_Iic 0).prod (convex_closedBall 0 ρ)
  have hne : (interior Ω).Nonempty := by
    rw [show Ω = Iic 0 ×ˢ closedBall (0 : X) ρ from rfl,
      interior_prod_eq, interior_Iic, interior_closedBall (0 : X) hρ.ne']
    exact ⟨(-1, 0), by simp [hρ]⟩
  have hunique := uniqueDiffOn_convex hconvex hne
  obtain ⟨σ, hσ, F, hF, hjets⟩ :=
    Poincare.AncientVolume.exists_smooth_subsequence_on_closed_convex
      hclosed hconvex hne f hf hbound
  have heq (m : ℕ) : EqOn (g m) (iteratedFDerivWithin ℝ m F Ω)
      (Iio 0 ×ˢ closedBall (0 : X) ρ) := by
    intro z hz
    apply tendsto_nhds_unique
      (((hinterior m {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at
        (mem_singleton z)).comp hσ.tendsto_atTop)
    exact (hjets m {z} isCompact_singleton
      (singleton_subset_iff.mpr ⟨le_of_lt (show z.1 < 0 from hz.1), hz.2⟩)).tendsto_at
        (mem_singleton z)
  refine ⟨F, hF, ?_⟩
  intro m K hK hKΩ
  apply tendstoUniformlyOn_past_of_time_lipschitz
    (U := closedBall (0 : X) ρ) ?_ ?_ ?_ hK hKΩ
  · intro A hA hAU
    exact (hinterior m A hA hAU).congr_right fun z hz => heq m (hAU hz)
  · intro x hx
    have hc := hF.continuousOn_iteratedFDerivWithin
      (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)) hunique
    exact hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht.2, hx⟩)
  · intro V hV hVU
    obtain ⟨B, hB, hBbound⟩ := hbound (Icc (-1) 0 ×ˢ V)
      (isCompact_Icc.prod hV) (prod_mono (fun _ ht => ht.2) hVU) (m + 1)
    refine ⟨B, hB, Eventually.of_forall fun k x hx s hs t ht => ?_⟩
    let Q : Set (ℝ × X) := Icc (-1) 0 ×ˢ {x}
    have hQ : Convex ℝ Q := (convex_Icc (-1) 0).prod (convex_singleton x)
    have hQΩ : Q ⊆ Ω := by
      rintro ⟨u, y⟩ ⟨hu, hy⟩
      rcases mem_singleton_iff.mp hy with rfl
      exact ⟨hu.2, hVU hx⟩
    have hdiff := (hf k).differentiableOn_iteratedFDerivWithin
      (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m) hunique
    have hnorm : ‖iteratedFDerivWithin ℝ m (f k) Ω (s, x) -
        iteratedFDerivWithin ℝ m (f k) Ω (t, x)‖ ≤ B * ‖(s, x) - (t, x)‖ := by
      apply hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => (hdiff z (hQΩ hz)).hasFDerivWithinAt.mono hQΩ)
        (fun z hz => ?_) ⟨ht, mem_singleton x⟩ ⟨hs, mem_singleton x⟩
      rw [norm_fderivWithin_iteratedFDerivWithin]
      apply hBbound k z
      exact ⟨hz.1, (mem_singleton_iff.mp hz.2) ▸ hx⟩
    simpa only [dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def,
      norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg (s - t))] using hnorm

end PoincareConjecture.AncientCompactness
