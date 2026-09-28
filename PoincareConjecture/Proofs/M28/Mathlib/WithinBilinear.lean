import PoincareConjecture.Proofs.M28.Mathlib.WithinConvergenceBounds
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BigOperators

theorem tendstoUniformlyOn_withinJets_bilinear
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {S : Set E} [LocallyCompactSpace S]
    (hconv : Convex ℝ S) (hS : UniqueDiffOn ℝ S) (B : F →L[ℝ] G →L[ℝ] H)
    {f : ℕ → E → F} {f₀ : E → F} {g : ℕ → E → G} {g₀ : E → G}
    (hf₀ : ContDiffOn ℝ ∞ f₀ S) (hg₀ : ContDiffOn ℝ ∞ g₀ S)
    (hf : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) S)
    (hg : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) S)
    (hfjet : ∀ m K, IsCompact K → K ⊆ S → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (f k) S)
      (iteratedFDerivWithin ℝ m f₀ S) atTop K)
    (hgjet : ∀ m K, IsCompact K → K ⊆ S → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (g k) S)
      (iteratedFDerivWithin ℝ m g₀ S) atTop K) :
    (∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun x => B (f k x) (g k x)) S) ∧
      ∀ m K, IsCompact K → K ⊆ S → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (fun x => B (f k x) (g k x)) S)
        (iteratedFDerivWithin ℝ m (fun x => B (f₀ x) (g₀ x)) S) atTop K := by
  have hsmooth : ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (fun x => B (f k x) (g k x)) S := by
    filter_upwards [hf, hg] with k hkf hkg
    exact B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hkf hkg
  have hpoint (x : E) (hx : x ∈ S) :
      Tendsto (fun k => B (f k x) (g k x)) atTop (𝓝 (B (f₀ x) (g₀ x))) := by
    have hfpoint : Tendsto (fun k => f k x) atTop (𝓝 (f₀ x)) := by
      have hz := (hfjet 0 {x} isCompact_singleton
        (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
      simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
        ((continuous_eval_const (0 : Fin 0 → E)).tendsto
          (iteratedFDerivWithin ℝ 0 f₀ S x)).comp hz
    have hgpoint : Tendsto (fun k => g k x) atTop (𝓝 (g₀ x)) := by
      have hz := (hgjet 0 {x} isCompact_singleton
        (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
      simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
        ((continuous_eval_const (0 : Fin 0 → E)).tendsto
          (iteratedFDerivWithin ℝ 0 g₀ S x)).comp hz
    exact (B.isBoundedBilinearMap.continuous.tendsto _).comp
      (hfpoint.prodMk_nhds hgpoint)
  have hbound : ∀ K, IsCompact K → K ⊆ S → ∀ m : ℕ,
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (fun y => B (f k y) (g k y)) S x‖ ≤ C := by
    intro K hK hKS m
    obtain ⟨A, hA, hAbound⟩ := exists_eventual_withinJet_bound_of_tendstoUniformlyOn
      hS hf₀ hK hKS (fun r => hfjet r K hK hKS) m
    obtain ⟨D, _, hDbound⟩ := exists_eventual_withinJet_bound_of_tendstoUniformlyOn
      hS hg₀ hK hKS (fun r => hgjet r K hK hKS) m
    refine ⟨‖B‖ * ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * A * D, ?_⟩
    filter_upwards [hf, hg, hAbound, hDbound] with k hkf hkg hkA hkD x hx
    apply (B.norm_iteratedFDerivWithin_le_of_bilinear hkf hkg hS (hKS hx)
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))).trans
    apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
    apply Finset.sum_le_sum
    intro r hr
    have hrm : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hkA r hrm x hx) (Nat.cast_nonneg _)
    · exact hkD (m - r) (Nat.sub_le _ _) x hx
    · exact norm_nonneg _
    · exact mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hA)
  exact ⟨hsmooth, fun m K hK hKS =>
    tendstoUniformlyOn_iteratedFDerivWithin_of_eventually_smooth
      hconv hS hpoint hsmooth hbound m hK hKS⟩
