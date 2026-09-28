import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Neighborhood

open Set Filter
open scoped Manifold Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.Conjugate.Realization

open RiemannianMetric ConnectionAlongCurve

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem exists_piece_realization
    {g : RiemannianMetric n M} {γ : ℝ → M} {V : ℝ → EuclideanSpace ℝ (Fin n)}
    {β : M} {L R r : ℝ} (hLR : L < R) (hr : 0 < r)
    (hgeo : g.IsGeodesicOn γ (Ioo (L - r) (R + r)))
    (hV : ∀ t ∈ Ioo (L - r) (R + r),
      ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    (hsrc : ∀ t ∈ Ioo (L - r) (R + r), γ t ∈ (extChartAt (𝓡 n) β).source)
    {η₀ η₁ : ℝ → M} {δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁)
    (hη₀ : g.IsGeodesicOn η₀ (Ioo (-δ₀) δ₀))
    (hη₁ : g.IsGeodesicOn η₁ (Ioo (-δ₁) δ₁))
    (hη₀0 : η₀ 0 = γ L) (hη₁0 : η₁ 0 = γ R)
    (hη₀v : HasDerivAt (fun s => extChartAt (𝓡 n) (γ L) (η₀ s)) (V L) 0)
    (hη₁v : HasDerivAt (fun s => extChartAt (𝓡 n) (γ R) (η₁ s)) (V R) 0) :
    ∃ (u : ℝ × ℝ → EuclideanSpace ℝ (Fin n)) (ρ ε : ℝ),
      0 < ρ ∧ ρ < r ∧ 0 < ε ∧ ContDiff ℝ 3 u ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (L - ρ) (R + ρ),
        u p ∈ (extChartAt (𝓡 n) β).target) ∧
      (∀ t ∈ Icc L R, ∀ᶠ s in 𝓝 t, u (0, s) = extChartAt (𝓡 n) β (γ s)) ∧
      (∀ t ∈ Icc L R, ∀ᶠ s in 𝓝 t,
        fderiv ℝ u (0, s) (1, 0) = chartField γ β V s) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), u (s, L) = extChartAt (𝓡 n) β (η₀ s) ∧
        η₀ s ∈ (extChartAt (𝓡 n) β).source) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), u (s, R) = extChartAt (𝓡 n) β (η₁ s) ∧
        η₁ s ∈ (extChartAt (𝓡 n) β).source) := by
  have hL : L ∈ Ioo (L - r) (R + r) := ⟨by linarith, by linarith⟩
  have hR : R ∈ Ioo (L - r) (R + r) := ⟨by linarith, by linarith⟩
  have hy : ContDiffOn ℝ 3 ((extChartAt (𝓡 n) β) ∘ γ) (Ioo (L - r) (R + r)) := by
    intro t ht
    exact ((contDiffAt_chart_curve (contMDiffAt_of_isGeodesicOn hgeo ht) (hsrc t ht)).of_le
      (show (3 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
  have hY : ContDiffOn ℝ 3 (chartField γ β V) (Ioo (L - r) (R + r)) := by
    intro t ht
    exact ((contDiffAt_chartField_change (contMDiffAt_of_isGeodesicOn hgeo ht)
      (mem_extChartAt_source _) (hsrc t ht) (hV t ht)).of_le
        (show (3 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
  obtain ⟨y, Vy, hy, hVy, hIcy, hVys, hey⟩ :=
    exists_contDiff_eqOn_of_contDiffOn_Ioo hy (by linarith) hLR.le (by linarith)
  obtain ⟨Y, VY, hY, hVY, hIcY, hVYs, heY⟩ :=
    exists_contDiff_eqOn_of_contDiffOn_Ioo hY (by linarith) hLR.le (by linarith)
  obtain ⟨c₀, hc₀, he₀, hs₀⟩ := exists_smooth_junction_reading hδ₀ hη₀
    (by simpa only [hη₀0] using hsrc L hL)
  obtain ⟨c₁, hc₁, he₁, hs₁⟩ := exists_smooth_junction_reading hδ₁ hη₁
    (by simpa only [hη₁0] using hsrc R hR)
  have h0₀ : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨by linarith, hδ₀⟩
  have h0₁ : (0 : ℝ) ∈ Ioo (-δ₁) δ₁ := ⟨by linarith, hδ₁⟩
  have hc₀0 : c₀ 0 = y L := by
    rw [he₀.eq_of_nhds, Function.comp_apply, hη₀0, hey (hIcy ⟨le_rfl, hLR.le⟩)]
    rfl
  have hc₁0 : c₁ 0 = y R := by
    rw [he₁.eq_of_nhds, Function.comp_apply, hη₁0, hey (hIcy ⟨hLR.le, le_rfl⟩)]
    rfl
  have hc₀v : HasDerivAt c₀ (Y L) 0 := by
    rw [heY (hIcY ⟨le_rfl, hLR.le⟩)]
    exact (hasDerivAt_junction_chart hη₀ h0₀ hη₀0 hη₀v (hsrc L hL)).congr_of_eventuallyEq he₀
  have hc₁v : HasDerivAt c₁ (Y R) 0 := by
    rw [heY (hIcY ⟨hLR.le, le_rfl⟩)]
    exact (hasDerivAt_junction_chart hη₁ h0₁ hη₁0 hη₁v (hsrc R hR)).congr_of_eventuallyEq he₁
  let u := chartVariation L R y Y c₀ c₁
  have hu : ContDiff ℝ 3 u := contDiff_chartVariation hLR.ne hy hY hc₀ hc₁
  have hu0 (t : ℝ) : u (0, t) = y t := chartVariation_zero hc₀0 hc₁0 t
  have huV (t : ℝ) : fderiv ℝ u (0, t) (1, 0) = Y t :=
    fderiv_chartVariation_snd_zero hLR.ne hc₀0 hc₁0 hc₀v hc₁v
      ((hy.differentiable (by norm_num)).differentiableAt)
      ((hY.differentiable (by norm_num)).differentiableAt)
  obtain ⟨ρ, hρ, hρsub⟩ := exists_Icc_enlarged_subset (hVy.inter hVY) hLR.le
    (fun t ht => ⟨hIcy ht, hIcY ht⟩)
  have hρr : ρ < r := by
    have h := hVys (hρsub (show L - ρ ∈ Icc (L - ρ) (R + ρ) from
      ⟨le_rfl, by linarith⟩)).1
    linarith [h.1]
  have hmem : ∀ t ∈ Icc (L - ρ) (R + ρ), u (0, t) ∈ (extChartAt (𝓡 n) β).target := by
    intro t ht
    rw [hu0, hey (hρsub ht).1]
    exact (extChartAt (𝓡 n) β).map_source (hsrc t (hVys (hρsub ht).1))
  obtain ⟨ε, hε, htube⟩ := exists_forall_mem_of_isCompact_of_continuous
    isCompact_Icc (isOpen_extChartAt_target β) hu.continuous hmem
  refine ⟨u, ρ, ε, hρ, hρr, hε, hu, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact htube s hs t (Ioo_subset_Icc_self ht)
  · intro t ht
    filter_upwards [hVy.mem_nhds (hIcy ht)] with s hs
    exact (hu0 s).trans (hey hs)
  · intro t ht
    filter_upwards [hVY.mem_nhds (hIcY ht)] with s hs
    exact (huV s).trans (heY hs)
  · filter_upwards [he₀, hs₀] with s hs hs'
    exact ⟨(chartVariation_left hLR.ne s).trans hs, hs'⟩
  · filter_upwards [he₁, hs₁] with s hs hs'
    exact ⟨(chartVariation_right hLR.ne s).trans hs, hs'⟩

end PoincareConjecture.Conjugate.Realization

end
