import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.CompactCutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sard.Nullity










set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold



theorem exists_compact_smooth_neighborhood
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (hn : Module.finrank ℝ E = n + 1) {C : Set M} (hC : IsCompact C) :
    ∃ (K : Set M) (CS : ChartedSpace (EuclideanHalfSpace (n + 1)) K),
      IsCompact K ∧ C ⊆ interior K ∧
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
        (EuclideanHalfSpace (n + 1)) _ (𝓡∂ (n + 1)) ∞ K _ CS ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ (n + 1)) 𝓘(ℝ, E) ∞
        (Subtype.val : K → M) := by
  obtain ⟨f, hf, _, _, _, _, hlevels⟩ :=
    exists_compact_smooth_cutoff (I := 𝓘(ℝ, E)) hC isOpen_univ (subset_univ C)
  obtain ⟨c, hc, hreg⟩ := exists_regular_value_in_interval_of_smooth hf
    (I := Ioo (0 : ℝ) 1) isOpen_Ioo ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨hK, hCK, _, _⟩ := hlevels c hc
  obtain ⟨K, CS, _, _, heq, _, hman, hemb⟩ :=
    exists_regular_superlevel_smooth_embedding hn hf c hreg
  exact ⟨K, CS, heq.symm ▸ hK, heq.symm ▸ hCK, hman, hemb⟩

end Poincare.Manifold
