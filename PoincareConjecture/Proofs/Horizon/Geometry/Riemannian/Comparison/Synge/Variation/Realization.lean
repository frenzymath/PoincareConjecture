import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Piece
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Partition

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold Topology ContDiff

namespace PoincareConjecture.Synge

open RiemannianMetric ConnectionAlongCurve Conjugate.Realization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

structure GeodesicVariation (g : RiemannianMetric n M) (γ : ℝ → M)
    (V : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ) (η₀ η₁ : ℝ → M) where
  N : ℕ
  τ : ℕ → ℝ
  β : ℕ → M
  u : ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin n)
  ρ : ℝ
  ε : ℝ
  η : ℕ → ℝ → M
  δ : ℕ → ℝ
  N_pos : 0 < N
  ρ_pos : 0 < ρ
  ε_pos : 0 < ε
  ε_le_ρ : ε ≤ ρ
  left : τ 0 = a
  right : τ N = b
  strict : ∀ i, τ i < τ (i + 1)
  time_mem : ∀ i ≤ N, τ i ∈ Icc a b
  smooth : ∀ i < N, ContDiff ℝ 3 (u i)
  tube : ∀ i < N, ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ρ) (τ (i + 1) + ρ),
    u i p ∈ (extChartAt (𝓡 n) (β i)).target
  base : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
    ∀ᶠ s in 𝓝 t, u i (0, s) = extChartAt (𝓡 n) (β i) (γ s)
  field : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
    fderiv ℝ (u i) (0, s) (1, 0) = chartField γ (β i) V s
  junction_left : ∀ i < N, ∀ᶠ s in 𝓝 (0 : ℝ),
    u i (s, τ i) = extChartAt (𝓡 n) (β i) (η i s) ∧
      η i s ∈ (extChartAt (𝓡 n) (β i)).source
  junction_right : ∀ i < N, ∀ᶠ s in 𝓝 (0 : ℝ),
    u i (s, τ (i + 1)) = extChartAt (𝓡 n) (β i) (η (i + 1) s) ∧
      η (i + 1) s ∈ (extChartAt (𝓡 n) (β i)).source
  δ_pos : ∀ j, 0 < δ j
  junction_geodesic : ∀ j, g.IsGeodesicOn (η j) (Ioo (-δ j) (δ j))
  endpoint_left : η 0 = η₀
  endpoint_right : η N = η₁
  base_source : ∀ i < N, ∀ t ∈ Icc (τ i - ρ) (τ (i + 1) + ρ),
    γ t ∈ (extChartAt (𝓡 n) (β i)).source

theorem exists_geodesicVariation [T2Space M]
    (g : RiemannianMetric n M) {γ : ℝ → M}
    {V : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ} {I : Set ℝ}
    (hab : a < b) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hgeo : g.IsGeodesicOn γ I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    {η₀ η₁ : ℝ → M} {δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁)
    (hη₀ : g.IsGeodesicOn η₀ (Ioo (-δ₀) δ₀))
    (hη₁ : g.IsGeodesicOn η₁ (Ioo (-δ₁) δ₁))
    (hη₀0 : η₀ 0 = γ a) (hη₁0 : η₁ 0 = γ b)
    (hη₀v : HasDerivAt (fun s => extChartAt (𝓡 n) (γ a) (η₀ s)) (V a) 0)
    (hη₁v : HasDerivAt (fun s => extChartAt (𝓡 n) (γ b) (η₁ s)) (V b) 0) :
    Nonempty (GeodesicVariation g γ V a b η₀ η₁) := by
  classical
  obtain ⟨N, τ, β, r, hN, hr, hτ0, hτN, hmono, hτmem, hslack⟩ :=
    exists_chart_partition_slack (I := 𝓡 n) hab hI hsub hgeo.contMDiffOn.continuousOn
  have hjunction (j : ℕ) : ∃ (δ : ℝ) (η : ℝ → M),
      0 < δ ∧ g.IsGeodesicOn η (Ioo (-δ) δ) ∧ η 0 = γ (τ j) ∧
      HasDerivAt (fun s => extChartAt (𝓡 n) (γ (τ j)) (η s)) (V (τ j)) 0 ∧
      (j = 0 → η = η₀) ∧ (j = N → η = η₁) := by
    by_cases hj0 : j = 0
    · subst j
      exact ⟨δ₀, η₀, hδ₀, hη₀, by simpa [hτ0] using hη₀0,
        by simpa [hτ0] using hη₀v, fun _ => rfl, fun h => (Nat.ne_of_gt hN h.symm).elim⟩
    · by_cases hjN : j = N
      · subst j
        exact ⟨δ₁, η₁, hδ₁, hη₁, by simpa [hτN] using hη₁0,
          by simpa [hτN] using hη₁v, fun h => (hj0 h).elim, fun _ => rfl⟩
      · obtain ⟨δ, η, hδ, hη, hη0, hηv, _⟩ :=
          exists_local_junction g (γ (τ j)) (V (τ j))
        exact ⟨δ, η, hδ, hη, hη0, hηv, fun h => (hj0 h).elim,
          fun h => (hjN h).elim⟩
  choose δ η hδ hη hη0 hηv hleft hright using hjunction
  have hpiece : ∀ i : ℕ, ∃ (u : ℝ × ℝ → EuclideanSpace ℝ (Fin n)) (ρ ε : ℝ), i < N →
      0 < ρ ∧ ρ < r ∧ 0 < ε ∧ ContDiff ℝ 3 u ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ρ) (τ (i + 1) + ρ),
        u p ∈ (extChartAt (𝓡 n) (β i)).target) ∧
      (∀ t ∈ Icc (τ i) (τ (i + 1)),
        ∀ᶠ s in 𝓝 t, u (0, s) = extChartAt (𝓡 n) (β i) (γ s)) ∧
      (∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
        fderiv ℝ u (0, s) (1, 0) = chartField γ (β i) V s) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), u (s, τ i) = extChartAt (𝓡 n) (β i) (η i s) ∧
        η i s ∈ (extChartAt (𝓡 n) (β i)).source) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), u (s, τ (i + 1)) =
        extChartAt (𝓡 n) (β i) (η (i + 1) s) ∧
          η (i + 1) s ∈ (extChartAt (𝓡 n) (β i)).source) := by
    intro i
    by_cases hi : i < N
    · obtain ⟨u, ρ, ε, hp⟩ := exists_piece_realization (hmono i) hr
        (fun t ht => hgeo t (hslack i hi t (Ioo_subset_Icc_self ht)).1)
        (fun t ht => hV t (hslack i hi t (Ioo_subset_Icc_self ht)).1)
        (fun t ht => by simpa only [extChartAt_source] using
          (hslack i hi t (Ioo_subset_Icc_self ht)).2.1)
        (hδ i) (hδ (i + 1)) (hη i) (hη (i + 1)) (hη0 i) (hη0 (i + 1))
        (hηv i) (hηv (i + 1))
      exact ⟨u, ρ, ε, fun _ => hp⟩
    · exact ⟨fun _ => 0, 1, 1, fun h => (hi h).elim⟩
  choose u ρf εf hp using hpiece
  have hne : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.mpr hN⟩
  let ρ := (Finset.range N).inf' hne ρf
  let ε := min ρ ((Finset.range N).inf' hne εf)
  have hρle (i : ℕ) (hi : i < N) : ρ ≤ ρf i := Finset.inf'_le _ (Finset.mem_range.mpr hi)
  have hεle (i : ℕ) (hi : i < N) : ε ≤ εf i :=
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.mpr hi))
  have hρ : 0 < ρ := (Finset.lt_inf'_iff _).mpr fun i hi => (hp i (Finset.mem_range.mp hi)).1
  have hε : 0 < ε := lt_min hρ
    ((Finset.lt_inf'_iff _).mpr fun i hi => (hp i (Finset.mem_range.mp hi)).2.2.1)
  refine ⟨{
    N := N, τ := τ, β := β, u := u, ρ := ρ, ε := ε, η := η, δ := δ
    N_pos := hN, ρ_pos := hρ, ε_pos := hε, ε_le_ρ := min_le_left _ _
    left := hτ0, right := hτN, strict := hmono, time_mem := hτmem
    smooth := fun i hi => (hp i hi).2.2.2.1
    tube := ?_, base := fun i hi => (hp i hi).2.2.2.2.2.1
    field := fun i hi => (hp i hi).2.2.2.2.2.2.1
    junction_left := fun i hi => (hp i hi).2.2.2.2.2.2.2.1
    junction_right := fun i hi => (hp i hi).2.2.2.2.2.2.2.2
    δ_pos := hδ, junction_geodesic := hη
    endpoint_left := hleft 0 rfl, endpoint_right := hright N rfl
    base_source := ?_ }⟩
  · rintro i hi ⟨s, t⟩ ⟨hs, ht⟩
    exact (hp i hi).2.2.2.2.1 (s, t) ⟨⟨by linarith [hs.1, hεle i hi],
      by linarith [hs.2, hεle i hi]⟩, ⟨by linarith [ht.1, hρle i hi],
      by linarith [ht.2, hρle i hi]⟩⟩
  · intro i hi t ht
    have hρr := (hρle i hi).trans_lt (hp i hi).2.1
    have htr : t ∈ Icc (τ i - r) (τ (i + 1) + r) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [extChartAt_source] using (hslack i hi t htr).2.1

end PoincareConjecture.Synge
