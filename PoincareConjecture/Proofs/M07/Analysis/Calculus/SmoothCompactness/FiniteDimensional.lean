import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Diagonal
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.DomainChange

set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem exists_common_smoothSubsequenceExtraction_finiteDimensional
    {E F : ℕ → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    {Ω : ∀ i, Set (E i)} (hΩ : ∀ i, IsOpen (Ω i))
    (f : ∀ i, ℕ → E i → F i)
    (hf : ∀ i k, ContDiffOn ℝ ∞ (f i k) (Ω i))
    (hbound : ∀ i K, IsCompact K → K ⊆ Ω i →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (f i k) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f₀ : ∀ i, E i → F i,
      (∀ i, ContDiffOn ℝ ∞ (f₀ i) (Ω i)) ∧
        ∀ i m K, IsCompact K → K ⊆ Ω i → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f i (σ k)))
          (iteratedFDeriv ℝ m (f₀ i)) atTop K := by
  let e : ∀ i, EuclideanSpace ℝ (Fin (Module.finrank ℝ (E i))) ≃L[ℝ] E i :=
    fun i => (toEuclidean (E := E i)).symm
  have hbound' (i : ℕ) : LocallyEventuallyBoundedDerivatives
      ((e i) ⁻¹' Ω i) (fun k => f i k ∘ e i) := by
    intro K hK hKΩ m
    obtain ⟨B, hB⟩ := hbound i (e i '' K) (hK.image (e i).continuous)
      (image_subset_iff.mpr hKΩ) m
    refine ⟨B * ‖(e i).toContinuousLinearMap‖ ^ m, ?_⟩
    filter_upwards [hB] with k hk x hx
    exact (norm_iteratedFDeriv_comp_continuousLinearEquiv_le (e i) (f i k) m x).trans
      (mul_le_mul_of_nonneg_right (hk (e i x) (mem_image_of_mem (e i) hx)) (by positivity))
  obtain ⟨σ, hσ, G, hG, hjet⟩ := exists_common_smoothSubsequenceExtraction
    (fun i => (hΩ i).preimage (e i).continuous) (fun i k => f i k ∘ e i)
    (fun i k => (hf i k).comp_continuousLinearMap (e i).toContinuousLinearMap) hbound'
  refine ⟨σ, hσ, (fun i => G i ∘ (e i).symm), ?_, ?_⟩
  · intro i
    have h := (hG i).comp_continuousLinearMap (e i).symm.toContinuousLinearMap
    simpa [Function.comp_def, ContinuousLinearEquiv.coe_coe] using h
  · intro i
    have h := compact_jet_convergence_comp_continuousLinearEquiv (e i).symm (hjet i)
    simpa [Function.comp_def] using h

end Poincare.Analysis.Calculus
