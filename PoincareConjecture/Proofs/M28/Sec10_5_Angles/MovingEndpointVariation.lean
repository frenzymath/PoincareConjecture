import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Piece
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Partition











open Set Filter
open scoped Manifold Topology ContDiff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.M28.Comparison

open RiemannianMetric ConnectionAlongCurve Conjugate.Realization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




structure MovingEndpointRealization (g : RiemannianMetric n M)
    (γ β : ℝ → M) (V : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ) where
  N : ℕ
  τ : ℕ → ℝ
  α : ℕ → M
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
    u i p ∈ (extChartAt (𝓡 n) (α i)).target
  base : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
    ∀ᶠ s in 𝓝 t, u i (0, s) = extChartAt (𝓡 n) (α i) (γ s)
  field : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
    fderiv ℝ (u i) (0, s) (1, 0) = chartField γ (α i) V s
  junction_left : ∀ i < N, ∀ᶠ s in 𝓝 (0 : ℝ),
    u i (s, τ i) = extChartAt (𝓡 n) (α i) (η i s) ∧
      η i s ∈ (extChartAt (𝓡 n) (α i)).source
  junction_right : ∀ i < N, ∀ᶠ s in 𝓝 (0 : ℝ),
    u i (s, τ (i + 1)) = extChartAt (𝓡 n) (α i) (η (i + 1) s) ∧
      η (i + 1) s ∈ (extChartAt (𝓡 n) (α i)).source
  δ_pos : ∀ j, 0 < δ j
  junction_geodesic : ∀ j, g.IsGeodesicOn (η j) (Ioo (-δ j) (δ j))
  junction_base : ∀ j, η j 0 = γ (τ j)
  fixed_left : ∀ s, η 0 s = γ a
  moving_right : ∀ s, η N s = β s
  base_source : ∀ i < N, ∀ t ∈ Icc (τ i - ρ) (τ (i + 1) + ρ),
    γ t ∈ (extChartAt (𝓡 n) (α i)).source



theorem exists_movingEndpointRealization [T2Space M]
    (g : RiemannianMetric n M) {γ β : ℝ → M}
    {V : ℝ → EuclideanSpace ℝ (Fin n)} {a b δβ : ℝ} {I : Set ℝ}
    (hab : a < b) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hgeo : g.IsGeodesicOn γ I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    (hleft : V a = 0) (hδβ : 0 < δβ)
    (hβ : g.IsGeodesicOn β (Ioo (-δβ) δβ))
    (hβ0 : β 0 = γ b)
    (hβv : HasDerivAt (fun s => extChartAt (𝓡 n) (γ b) (β s)) (V b) 0) :
    Nonempty (MovingEndpointRealization g γ β V a b) := by
  classical
  obtain ⟨N, τ, α, r, hN, hr, hτ0, hτN, hmono, hτmem, hslack⟩ :=
    exists_chart_partition_slack (I := 𝓡 n) hab hI hsub
      hgeo.contMDiffOn.continuousOn
  choose δ₀ η₀ hδ₀ hη₀ hη₀0 hη₀v hη₀const using
    (fun j : ℕ => exists_local_junction g (γ (τ j)) (V (τ j)))
  let δ : ℕ → ℝ := fun j => if j = N then δβ else δ₀ j
  let η : ℕ → ℝ → M := fun j => if j = N then β else η₀ j
  have hδ (j : ℕ) : 0 < δ j := by
    by_cases hj : j = N
    · simpa [δ, hj] using hδβ
    · simpa [δ, hj] using hδ₀ j
  have hη (j : ℕ) : g.IsGeodesicOn (η j) (Ioo (-δ j) (δ j)) := by
    by_cases hj : j = N
    · simpa [η, δ, hj] using hβ
    · simpa [η, δ, hj] using hη₀ j
  have hη0 (j : ℕ) : η j 0 = γ (τ j) := by
    by_cases hj : j = N
    · simpa [η, hj, hτN] using hβ0
    · simpa [η, hj] using hη₀0 j
  have hηv (j : ℕ) :
      HasDerivAt (fun s => extChartAt (𝓡 n) (γ (τ j)) (η j s)) (V (τ j)) 0 := by
    by_cases hj : j = N
    · simpa [η, hj, hτN] using hβv
    · simpa [η, hj] using hη₀v j
  have hpiece : ∀ i : ℕ, ∃ (u : ℝ × ℝ → EuclideanSpace ℝ (Fin n)) (ρ ε : ℝ),
      i < N → 0 < ρ ∧ ρ < r ∧ 0 < ε ∧ ContDiff ℝ 3 u ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ρ) (τ (i + 1) + ρ),
        u p ∈ (extChartAt (𝓡 n) (α i)).target) ∧
      (∀ t ∈ Icc (τ i) (τ (i + 1)),
        ∀ᶠ s in 𝓝 t, u (0, s) = extChartAt (𝓡 n) (α i) (γ s)) ∧
      (∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
        fderiv ℝ u (0, s) (1, 0) = chartField γ (α i) V s) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), u (s, τ i) = extChartAt (𝓡 n) (α i) (η i s) ∧
        η i s ∈ (extChartAt (𝓡 n) (α i)).source) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ),
        u (s, τ (i + 1)) = extChartAt (𝓡 n) (α i) (η (i + 1) s) ∧
          η (i + 1) s ∈ (extChartAt (𝓡 n) (α i)).source) := by
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
  have hρle (i : ℕ) (hi : i < N) : ρ ≤ ρf i :=
    Finset.inf'_le _ (Finset.mem_range.mpr hi)
  have hεle (i : ℕ) (hi : i < N) : ε ≤ εf i :=
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.mpr hi))
  have hρ : 0 < ρ := (Finset.lt_inf'_iff _).mpr fun i hi =>
    (hp i (Finset.mem_range.mp hi)).1
  have hε : 0 < ε := lt_min hρ ((Finset.lt_inf'_iff _).mpr fun i hi =>
    (hp i (Finset.mem_range.mp hi)).2.2.1)
  refine ⟨{
    N := N, τ := τ, α := α, u := u, ρ := ρ, ε := ε, η := η, δ := δ
    N_pos := hN, ρ_pos := hρ, ε_pos := hε, ε_le_ρ := min_le_left _ _
    left := hτ0, right := hτN, strict := hmono, time_mem := hτmem
    smooth := fun i hi => (hp i hi).2.2.2.1
    tube := ?_, base := fun i hi => (hp i hi).2.2.2.2.2.1
    field := fun i hi => (hp i hi).2.2.2.2.2.2.1
    junction_left := fun i hi => (hp i hi).2.2.2.2.2.2.2.1
    junction_right := fun i hi => (hp i hi).2.2.2.2.2.2.2.2
    δ_pos := hδ, junction_geodesic := hη, junction_base := hη0
    fixed_left := ?_, moving_right := ?_, base_source := ?_ }⟩
  · rintro i hi ⟨s, t⟩ ⟨hs, ht⟩
    exact (hp i hi).2.2.2.2.1 (s, t) ⟨⟨by linarith [hs.1, hεle i hi],
      by linarith [hs.2, hεle i hi]⟩, ⟨by linarith [ht.1, hρle i hi],
      by linarith [ht.2, hρle i hi]⟩⟩
  · intro s
    have h0N : (0 : ℕ) ≠ N := by omega
    have hv : V (τ 0) = 0 := by rw [hτ0]; exact hleft
    simpa [η, h0N, hτ0] using hη₀const 0 hv s
  · intro s
    simp [η]
  · intro i hi t ht
    have hρr := (hρle i hi).trans_lt (hp i hi).2.1
    have htr : t ∈ Icc (τ i - r) (τ (i + 1) + r) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [extChartAt_source] using (hslack i hi t htr).2.1

end PoincareConjecture.M28.Comparison
end
