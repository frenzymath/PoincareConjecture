import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Piece
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Partition

open Set Filter
open scoped Manifold Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.Conjugate.Realization

open RiemannianMetric ConnectionAlongCurve

theorem glueField_eq_piece {F : Type*} {V₀ V₁ : ℝ → F} {c : ℝ}
    (hmatch : V₀ c = V₁ c) {τ : ℕ → ℝ} {k i : ℕ}
    (hmono : ∀ j, τ j < τ (j + 1)) (hτk : τ k = c)
    {s : ℝ} (hs : s ∈ Icc (τ i) (τ (i + 1))) :
    (if s ≤ c then V₀ s else V₁ s) = (if i < k then V₀ else V₁) s := by
  have hm : Monotone τ := (strictMono_nat_of_lt_succ hmono).monotone
  by_cases hi : i < k
  · have hsc : s ≤ c := hs.2.trans ((hm (by omega)).trans_eq hτk)
    simp only [if_pos hi, if_pos hsc]
  · have hcs : c ≤ s := hτk.symm.trans_le ((hm (by omega)).trans hs.1)
    rw [if_neg hi]
    by_cases hsc : s ≤ c
    · have heq : s = c := le_antisymm hsc hcs
      simpa only [heq, if_pos le_rfl] using hmatch
    · rw [if_neg hsc]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

structure BrokenRealization (g : RiemannianMetric n M) (γ : ℝ → M)
    (V₀ V₁ : ℝ → EuclideanSpace ℝ (Fin n)) (a c b : ℝ) where
  N : ℕ
  τ : ℕ → ℝ
  β : ℕ → M
  u : ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin n)
  ρ : ℝ
  ε : ℝ
  k : ℕ
  η : ℕ → ℝ → M
  δ : ℕ → ℝ
  N_pos : 0 < N
  ρ_pos : 0 < ρ
  ε_pos : 0 < ε
  ε_le_ρ : ε ≤ ρ
  k_pos : 0 < k
  k_lt : k < N
  left : τ 0 = a
  right : τ N = b
  corner : τ k = c
  strict : ∀ i, τ i < τ (i + 1)
  time_mem : ∀ i ≤ N, τ i ∈ Icc a b
  smooth : ∀ i < N, ContDiff ℝ 3 (u i)
  tube : ∀ i < N, ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ρ) (τ (i + 1) + ρ),
    u i p ∈ (extChartAt (𝓡 n) (β i)).target
  base : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
    ∀ᶠ s in 𝓝 t, u i (0, s) = extChartAt (𝓡 n) (β i) (γ s)
  field : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
    fderiv ℝ (u i) (0, s) (1, 0) = chartField γ (β i) (if i < k then V₀ else V₁) s
  junction_left : ∀ i < N, ∀ᶠ s in 𝓝 (0 : ℝ),
    u i (s, τ i) = extChartAt (𝓡 n) (β i) (η i s) ∧
      η i s ∈ (extChartAt (𝓡 n) (β i)).source
  junction_right : ∀ i < N, ∀ᶠ s in 𝓝 (0 : ℝ),
    u i (s, τ (i + 1)) = extChartAt (𝓡 n) (β i) (η (i + 1) s) ∧
      η (i + 1) s ∈ (extChartAt (𝓡 n) (β i)).source
  δ_pos : ∀ j, 0 < δ j
  junction_geodesic : ∀ j, g.IsGeodesicOn (η j) (Ioo (-δ j) (δ j))
  junction_base : ∀ j, η j 0 = γ (τ j)
  fixed_left : ∀ s, η 0 s = γ a
  fixed_right : ∀ s, η N s = γ b
  base_source : ∀ i < N, ∀ t ∈ Icc (τ i - ρ) (τ (i + 1) + ρ),
    γ t ∈ (extChartAt (𝓡 n) (β i)).source

theorem exists_broken_realization [T2Space M]
    (g : RiemannianMetric n M) {γ : ℝ → M}
    {V₀ V₁ : ℝ → EuclideanSpace ℝ (Fin n)} {a c b : ℝ} {I : Set ℝ}
    (hac : a < c) (hcb : c < b) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hgeo : g.IsGeodesicOn γ I)
    (hV₀ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₀) t)
    (hV₁ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₁) t)
    (hmatch : V₀ c = V₁ c) (hleft : V₀ a = 0) (hright : V₁ b = 0) :
    Nonempty (BrokenRealization g γ V₀ V₁ a c b) := by
  classical
  obtain ⟨N, τ, β, r, k, hN, hr, hτ0, hτN, hk0, hkN, hτk, hmono, hτmem, hslack⟩ :=
    exists_chart_partition_slack_through (I := 𝓡 n) hac hcb hI hsub hgeo.contMDiffOn.continuousOn
  let V : ℝ → EuclideanSpace ℝ (Fin n) := fun t => if t ≤ c then V₀ t else V₁ t
  choose δ η hδ hη hη0 hηv hηconst using
    (fun j : ℕ => exists_local_junction g (γ (τ j)) (V (τ j)))
  have hVpiece (i : ℕ) {t : ℝ} (ht : t ∈ Icc (τ i) (τ (i + 1))) :
      V t = (if i < k then V₀ else V₁) t := glueField_eq_piece hmatch hmono hτk ht
  have hpiece : ∀ i : ℕ, ∃ (u : ℝ × ℝ → EuclideanSpace ℝ (Fin n)) (ρ ε : ℝ), i < N →
      0 < ρ ∧ ρ < r ∧ 0 < ε ∧ ContDiff ℝ 3 u ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ρ) (τ (i + 1) + ρ),
        u p ∈ (extChartAt (𝓡 n) (β i)).target) ∧
      (∀ t ∈ Icc (τ i) (τ (i + 1)),
        ∀ᶠ s in 𝓝 t, u (0, s) = extChartAt (𝓡 n) (β i) (γ s)) ∧
      (∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
        fderiv ℝ u (0, s) (1, 0) = chartField γ (β i) (if i < k then V₀ else V₁) s) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), u (s, τ i) = extChartAt (𝓡 n) (β i) (η i s) ∧
        η i s ∈ (extChartAt (𝓡 n) (β i)).source) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), u (s, τ (i + 1)) =
        extChartAt (𝓡 n) (β i) (η (i + 1) s) ∧
          η (i + 1) s ∈ (extChartAt (𝓡 n) (β i)).source) := by
    intro i
    by_cases hi : i < N
    · have hVi : ∀ t ∈ Ioo (τ i - r) (τ (i + 1) + r),
          ContDiffAt ℝ ∞ (chartField γ (γ t) (if i < k then V₀ else V₁)) t := by
        intro t ht
        by_cases hik : i < k
        · rw [if_pos hik]; exact hV₀ t (hslack i hi t (Ioo_subset_Icc_self ht)).1
        · rw [if_neg hik]; exact hV₁ t (hslack i hi t (Ioo_subset_Icc_self ht)).1
      obtain ⟨u, ρ, ε, hp⟩ := exists_piece_realization (hmono i) hr
        (fun t ht => hgeo t (hslack i hi t (Ioo_subset_Icc_self ht)).1) hVi
        (fun t ht => by simpa only [extChartAt_source] using
          (hslack i hi t (Ioo_subset_Icc_self ht)).2.1)
        (hδ i) (hδ (i + 1)) (hη i) (hη (i + 1)) (hη0 i) (hη0 (i + 1))
        (by rw [← hVpiece i ⟨le_rfl, (hmono i).le⟩]; exact hηv i)
        (by rw [← hVpiece i ⟨(hmono i).le, le_rfl⟩]; exact hηv (i + 1))
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
    N := N, τ := τ, β := β, u := u, ρ := ρ, ε := ε, k := k, η := η, δ := δ
    N_pos := hN, ρ_pos := hρ, ε_pos := hε, ε_le_ρ := min_le_left _ _
    k_pos := hk0, k_lt := hkN, left := hτ0, right := hτN, corner := hτk
    strict := hmono, time_mem := hτmem, smooth := fun i hi => (hp i hi).2.2.2.1
    tube := ?_, base := fun i hi => (hp i hi).2.2.2.2.2.1
    field := fun i hi => (hp i hi).2.2.2.2.2.2.1
    junction_left := fun i hi => (hp i hi).2.2.2.2.2.2.2.1
    junction_right := fun i hi => (hp i hi).2.2.2.2.2.2.2.2
    δ_pos := hδ, junction_geodesic := hη, junction_base := hη0
    fixed_left := ?_, fixed_right := ?_, base_source := ?_ }⟩
  · rintro i hi ⟨s, t⟩ ⟨hs, ht⟩
    exact (hp i hi).2.2.2.2.1 (s, t) ⟨⟨by linarith [hs.1, hεle i hi],
      by linarith [hs.2, hεle i hi]⟩, ⟨by linarith [ht.1, hρle i hi],
      by linarith [ht.2, hρle i hi]⟩⟩
  · intro s
    have hv : V (τ 0) = 0 := by simp only [V, hτ0, if_pos hac.le, hleft]
    simpa only [hτ0] using hηconst 0 hv s
  · intro s
    have hv : V (τ N) = 0 := by simp only [V, hτN, if_neg (not_le.mpr hcb), hright]
    simpa only [hτN] using hηconst N hv s
  · intro i hi t ht
    have hρr := (hρle i hi).trans_lt (hp i hi).2.1
    have htr : t ∈ Icc (τ i - r) (τ (i + 1) + r) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [extChartAt_source] using (hslack i hi t htr).2.1

end PoincareConjecture.Conjugate.Realization

end
