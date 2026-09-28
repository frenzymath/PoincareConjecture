import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Partition


noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [SigmaCompactSpace M]



theorem exists_finite_spacetime_chart_decomposition
    {φ : M × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∃ (s : Finset M) (w : M → M × ℝ → ℝ),
      (∀ i, ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (w i)) ∧
      (∀ i, HasCompactSupport (w i)) ∧
      (∀ i, tsupport (w i) ⊆ tsupport φ) ∧
      (∀ i, tsupport (w i) ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) i).source ×ˢ univ) ∧
      (∀ i z, 0 ≤ φ z → 0 ≤ w i z) ∧
      ∀ z, ∑ i ∈ s, w i z = φ z := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (𝓡 n) M
  have hfinite := ρ.locallyFinite.finite_nonempty_inter_compact
    (hφc.isCompact.image continuous_fst)
  refine ⟨hfinite.toFinset, fun i z => ρ i z.1 * φ z,
    (fun i => ((ρ i).contMDiff.comp contMDiff_fst).mul hφ),
    (fun _ => hφc.mul_left), (fun _ => tsupport_mul_subset_right), ?_,
    (fun i z hz => mul_nonneg (ρ.nonneg i z.1) hz), ?_⟩
  · intro i
    have hs : tsupport (fun z : M × ℝ => ρ i z.1 * φ z) ⊆
        Prod.fst ⁻¹' tsupport (ρ i) := by
      apply closure_minimal ?_ ((isClosed_tsupport _).preimage continuous_fst)
      intro z hz
      exact subset_tsupport _ (mul_ne_zero_iff.mp hz).1
    intro z hz
    exact ⟨hρ i (hs hz), mem_univ _⟩
  · intro z
    have hs : Function.support (fun i => ρ i z.1 * φ z) ⊆ hfinite.toFinset := by
      intro i hi
      apply hfinite.mem_toFinset.mpr
      refine ⟨z.1, (mul_ne_zero_iff.mp hi).1, ?_⟩
      exact mem_image_of_mem Prod.fst (subset_tsupport φ (mul_ne_zero_iff.mp hi).2)
    rw [← finsum_eq_sum_of_support_subset _ hs, ← finsum_mul,
      ρ.sum_eq_one (mem_univ z.1), one_mul]

end PoincareConjecture
