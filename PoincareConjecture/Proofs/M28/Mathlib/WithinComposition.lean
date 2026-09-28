import PoincareConjecture.Proofs.M28.Mathlib.WithinConvergenceBounds
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Bounds










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology




theorem tendstoUniformlyOn_withinJets_comp_of_compact_capture
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {S : Set E} {T : Set F} [LocallyCompactSpace S]
    (hconv : Convex ℝ S) (hS : UniqueDiffOn ℝ S) (hT : UniqueDiffOn ℝ T)
    {f : ℕ → F → G} {f₀ : F → G} {a : ℕ → E → F} {a₀ : E → F}
    (hf₀ : ContDiffOn ℝ ∞ f₀ T) (ha₀ : ContDiffOn ℝ ∞ a₀ S)
    (hf : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) T)
    (ha : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) S)
    (hmap : ∀ᶠ k in atTop, MapsTo (a k) S T) (hmap₀ : MapsTo a₀ S T)
    (hcapture : ∀ K, IsCompact K → K ⊆ S → ∃ C : Set F,
      IsCompact C ∧ C ⊆ T ∧ ∀ᶠ k in atTop, MapsTo (a k) K C)
    (hfjet : ∀ m K, IsCompact K → K ⊆ T → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (f k) T)
      (iteratedFDerivWithin ℝ m f₀ T) atTop K)
    (hajet : ∀ m K, IsCompact K → K ⊆ S → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (a k) S)
      (iteratedFDerivWithin ℝ m a₀ S) atTop K) :
    (∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ a k) S) ∧
      ∀ m K, IsCompact K → K ⊆ S → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f k ∘ a k) S)
        (iteratedFDerivWithin ℝ m (f₀ ∘ a₀) S) atTop K := by
  have hsmooth : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ a k) S := by
    filter_upwards [hf, ha, hmap] with k hkf hka hkmap
    exact hkf.comp hka hkmap
  have hapoint (x : E) (hx : x ∈ S) :
      Tendsto (fun k => a k x) atTop (𝓝 (a₀ x)) := by
    have hz := (hajet 0 {x} isCompact_singleton
      (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
      ((continuous_eval_const (0 : Fin 0 → E)).tendsto
        (iteratedFDerivWithin ℝ 0 a₀ S x)).comp hz
  have hpoint (x : E) (hx : x ∈ S) :
      Tendsto (fun k => (f k ∘ a k) x) atTop (𝓝 ((f₀ ∘ a₀) x)) := by
    obtain ⟨C, hC, hCT, hcap⟩ := hcapture {x} isCompact_singleton
      (singleton_subset_iff.mpr hx)
    have hzero : TendstoUniformlyOn f f₀ atTop C := by
      simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → F)).comp_tendstoUniformlyOn (hfjet 0 C hC hCT)
    exact hzero.tendsto_comp ((hf₀.continuousOn _ (hmap₀ hx)).mono hCT)
      (tendsto_nhdsWithin_iff.mpr ⟨hapoint x hx,
        hcap.mono fun k hk => hk (mem_singleton x)⟩)
  have hbound : ∀ K, IsCompact K → K ⊆ S → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f k ∘ a k) S x‖ ≤ B := by
    intro K hK hKS m
    obtain ⟨C, hC, hCT, hcap⟩ := hcapture K hK hKS
    obtain ⟨A, _, hA⟩ := exists_eventual_withinJet_bound_of_tendstoUniformlyOn
      hT hf₀ hC hCT (fun r => hfjet r C hC hCT) m
    obtain ⟨D, hD, hDbound⟩ := exists_eventual_withinJet_bound_of_tendstoUniformlyOn
      hS ha₀ hK hKS (fun r => hajet r K hK hKS) m
    refine ⟨m.factorial * A * D ^ m, ?_⟩
    filter_upwards [hf, ha, hmap, hcap, hA, hDbound] with k hkf hka hkmap hkcap hkA hkD x hx
    apply norm_iteratedFDerivWithin_comp_le hkf hka
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)) hT hS hkmap (hKS hx)
    · intro r hr
      exact hkA r hr _ (hkcap hx)
    · intro r hr hrm
      exact (hkD r hrm x hx).trans (le_self_pow₀ hD (Nat.ne_of_gt hr))
  exact ⟨hsmooth, fun m K hK hKS =>
    tendstoUniformlyOn_iteratedFDerivWithin_of_eventually_smooth
      hconv hS hpoint hsmooth hbound m hK hKS⟩
