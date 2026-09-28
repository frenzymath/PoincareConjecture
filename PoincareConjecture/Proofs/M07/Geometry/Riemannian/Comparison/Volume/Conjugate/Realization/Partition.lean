import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Manifold
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas




















open Set Metric
open scoped Manifold Topology ContDiff

noncomputable section

namespace PoincareConjecture.Conjugate.Realization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem exists_chart_partition_slack {γ : ℝ → M} {O : Set ℝ} {a b : ℝ}
    (hab : a < b) (hO : IsOpen O) (hKO : Icc a b ⊆ O) (hγ : ContinuousOn γ O) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (α : ℕ → M) (r : ℝ),
      0 < N ∧ 0 < r ∧ τ 0 = a ∧ τ N = b ∧
      (∀ i, τ i < τ (i + 1)) ∧
      (∀ i ≤ N, τ i ∈ Icc a b) ∧
      (∀ i < N, ∀ t ∈ Icc (τ i - r) (τ (i + 1) + r),
        t ∈ O ∧ γ t ∈ (chartAt H (α i)).source ∧
          extChartAt I (α i) (γ t) ∈ (extChartAt I (α i)).target) := by
  classical
  have hMne : Nonempty M := ⟨γ a⟩
  set c : M → Set ℝ := fun x => O ∩ γ ⁻¹' (chartAt H x).source with hc
  have hcopen : ∀ x : M, IsOpen (c x) := fun x =>
    hγ.isOpen_inter_preimage hO (chartAt H x).open_source
  have hcover : Icc a b ⊆ ⋃ x : M, c x := fun t ht =>
    mem_iUnion.2 ⟨γ t, hKO ht, mem_chart_source H (γ t)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hcopen hcover
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (b - a) / δ)
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero] at hN
      have hpos : 0 < 4 * (b - a) / δ := by positivity
      linarith
    · exact h0
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  set h : ℝ := (b - a) / N with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hNb : (N : ℝ) * h = b - a := by rw [hh]; field_simp
  have hhδ : h < δ / 4 := by
    have h4 : 4 * (b - a) < δ * N := by
      have := (div_lt_iff₀ hδ).mp hN
      linarith
    rw [hh, div_lt_iff₀ hNR]
    nlinarith [h4]
  set τ : ℕ → ℝ := fun i => a + i * h with hτdef
  set r : ℝ := δ / 4 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hτ0 : τ 0 = a := by simp [hτdef]
  have hτN : τ N = b := by
    simp only [hτdef]
    linarith [hNb]
  have hτmono : ∀ i, τ i < τ (i + 1) := by
    intro i
    simp only [hτdef]
    push_cast
    nlinarith [hhpos]
  have hτmem : ∀ i ≤ N, τ i ∈ Icc a b := by
    intro i hi
    have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    constructor
    · have : 0 ≤ (i : ℝ) * h := by positivity
      simp only [hτdef]; linarith
    · have : (i : ℝ) * h ≤ (N : ℝ) * h := by nlinarith [hhpos]
      simp only [hτdef]; linarith
  have hex : ∀ i : ℕ, ∃ x : M, i < N → ball (τ i) δ ⊆ c x := by
    intro i
    by_cases hi : i < N
    · obtain ⟨x, hx⟩ := hball (τ i) (hτmem i hi.le)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨Classical.arbitrary M, fun hc => absurd hc hi⟩
  choose α hα using hex
  refine ⟨N, τ, α, r, hNpos, hrpos, hτ0, hτN, hτmono, hτmem, ?_⟩
  intro i hi t ht
  have hstep : τ (i + 1) = τ i + h := by
    simp only [hτdef]; push_cast; ring
  have htball : t ∈ ball (τ i) δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    obtain ⟨ht1, ht2⟩ := ht
    rw [hstep] at ht2
    constructor
    · rw [hr] at ht1; linarith
    · rw [hr] at ht2; linarith
  have hmem : t ∈ c (α i) := hα i hi htball
  refine ⟨hmem.1, hmem.2, ?_⟩
  exact (extChartAt I (α i)).map_source (by rw [extChartAt_source]; exact hmem.2)

theorem exists_chart_partition_slack_through {γ : ℝ → M} {O : Set ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hO : IsOpen O) (hKO : Icc a b ⊆ O)
    (hγ : ContinuousOn γ O) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (α : ℕ → M) (r : ℝ) (k : ℕ),
      0 < N ∧ 0 < r ∧ τ 0 = a ∧ τ N = b ∧
      0 < k ∧ k < N ∧ τ k = c ∧
      (∀ i, τ i < τ (i + 1)) ∧
      (∀ i ≤ N, τ i ∈ Icc a b) ∧
      (∀ i < N, ∀ t ∈ Icc (τ i - r) (τ (i + 1) + r),
        t ∈ O ∧ γ t ∈ (chartAt H (α i)).source ∧
          extChartAt I (α i) (γ t) ∈ (extChartAt I (α i)).target) := by
  have hIcc1 : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb.le
  have hIcc2 : Icc c b ⊆ Icc a b := Icc_subset_Icc hac.le le_rfl
  obtain ⟨N₁, τ₁, α₁, r₁, hN₁, hr₁, hτ₁0, hτ₁N, hmono₁, hmem₁, hpiece₁⟩ :=
    exists_chart_partition_slack (I := I) hac hO (hIcc1.trans hKO) hγ
  obtain ⟨N₂, τ₂, α₂, r₂, hN₂, hr₂, hτ₂0, hτ₂N, hmono₂, hmem₂, hpiece₂⟩ :=
    exists_chart_partition_slack (I := I) hcb hO (hIcc2.trans hKO) hγ
  let τ : ℕ → ℝ := fun i => if i ≤ N₁ then τ₁ i else τ₂ (i - N₁)
  let α : ℕ → M := fun i => if i < N₁ then α₁ i else α₂ (i - N₁)
  have hτ_le : ∀ i, i ≤ N₁ → τ i = τ₁ i := by
    intro i hi; exact if_pos hi
  have hτ_ge : ∀ i, N₁ ≤ i → τ i = τ₂ (i - N₁) := by
    intro i hi
    rcases eq_or_lt_of_le hi with heq | hlt
    · rw [← heq, hτ_le N₁ le_rfl, hτ₁N, Nat.sub_self, hτ₂0]
    · exact if_neg (by omega)
  have hα_lt : ∀ i, i < N₁ → α i = α₁ i := by
    intro i hi; exact if_pos hi
  have hα_ge : ∀ i, N₁ ≤ i → α i = α₂ (i - N₁) := by
    intro i hi; exact if_neg (by omega)
  refine ⟨N₁ + N₂, τ, α, min r₁ r₂, N₁, by omega, lt_min hr₁ hr₂,
    (hτ_le 0 (Nat.zero_le _)).trans hτ₁0, ?_, hN₁, by omega,
    (hτ_le N₁ le_rfl).trans hτ₁N, ?_, ?_, ?_⟩
  · rw [hτ_ge (N₁ + N₂) (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hτ₂N]
  · intro i
    by_cases h : i + 1 ≤ N₁
    · rw [hτ_le i (by omega), hτ_le (i + 1) h]
      exact hmono₁ i
    · rw [hτ_ge i (by omega), hτ_ge (i + 1) (by omega)]
      have heq : i + 1 - N₁ = (i - N₁) + 1 := by omega
      rw [heq]
      exact hmono₂ (i - N₁)
  · intro i hi
    by_cases h : i ≤ N₁
    · rw [hτ_le i h]
      exact hIcc1 (hmem₁ i h)
    · rw [hτ_ge i (by omega)]
      exact hIcc2 (hmem₂ (i - N₁) (by omega))
  · intro i hi t ht
    by_cases h : i < N₁
    · rw [hτ_le i h.le, hτ_le (i + 1) h] at ht
      rw [hα_lt i h]
      exact hpiece₁ i h t ⟨by linarith [ht.1, min_le_left r₁ r₂],
        by linarith [ht.2, min_le_left r₁ r₂]⟩
    · have e2 : τ (i + 1) = τ₂ ((i - N₁) + 1) := by
        rw [hτ_ge (i + 1) (by omega)]
        congr 1; omega
      rw [hτ_ge i (by omega), e2] at ht
      rw [hα_ge i (by omega)]
      exact hpiece₂ (i - N₁) (by omega) t ⟨by linarith [ht.1, min_le_right r₁ r₂],
        by linarith [ht.2, min_le_right r₁ r₂]⟩

end PoincareConjecture.Conjugate.Realization

end
