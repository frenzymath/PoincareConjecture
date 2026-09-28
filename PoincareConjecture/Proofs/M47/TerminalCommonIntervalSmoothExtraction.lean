import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.FiniteDimensional










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped ContDiff Topology

universe u v

namespace PoincareConjecture.M47

theorem terminalCommonInterval_smooth_row_extraction
    {E F : ℕ → Type u}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    {Ω : ∀ i, Set (E i)} (hΩ : ∀ i, IsOpen (Ω i))
    (f : ∀ i, ℕ → E i → F i)
    (hf : ∀ i k, ContDiffOn ℝ ∞ (f i k) (Ω i))
    (hbound : ∀ i K, IsCompact K → K ⊆ Ω i → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f i k) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f₀ : ∀ i, E i → F i,
      (∀ i, ContDiffOn ℝ ∞ (f₀ i) (Ω i)) ∧
      ∀ i m K, IsCompact K → K ⊆ Ω i → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f i (σ k)))
        (iteratedFDeriv ℝ m (f₀ i)) atTop K := by
  exact exists_common_smoothSubsequenceExtraction_finiteDimensional hΩ f hf hbound

end PoincareConjecture.M47
