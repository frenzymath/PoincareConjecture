import PoincareConjecture.Proofs.M76.Brown.BicollarOpenHalves

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S A C K : Set X}

theorem exists_bicollar_restriction
    (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) (hC : IsOpen C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (hside : ∀ z, (H z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ))
    (hAS : A ⊆ S) (hA : IsOpen ((Subtype.val : S → X) ⁻¹' A)) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ C ∧
      ∃ G : (A × Ioo (-1 : ℝ) 1) ≃ₜ U,
        (∀ z, (G z : X) = (H (Set.inclusion hAS z.1, z.2) : X)) ∧
        (∀ a, (G (bicollarBase a) : X) = (a : X)) ∧
        ∀ z, (G z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ) := by
  let f : (A × Ioo (-1 : ℝ) 1) → X :=
    (Subtype.val : C → X) ∘ H ∘ Prod.map (Set.inclusion hAS) id
  have hf : Topology.IsOpenEmbedding f := hC.isOpenEmbedding_subtypeVal.comp
    (H.isOpenEmbedding.comp
      ((Topology.IsOpenEmbedding.inclusion hAS hA).prodMap .id))
  let G : (A × Ioo (-1 : ℝ) 1) ≃ₜ range f := hf.isEmbedding.toHomeomorph
  have hG (z : A × Ioo (-1 : ℝ) 1) :
      (G z : X) = (H (Set.inclusion hAS z.1, z.2) : X) := rfl
  have hGbase (a : A) : (G (bicollarBase a) : X) = (a : X) :=
    (hG (bicollarBase a)).trans (hbase (Set.inclusion hAS a))
  refine ⟨range f, hf.isOpen_range, ?_, ?_, G, hG, hGbase, ?_⟩
  · intro x hx
    exact ⟨bicollarBase (⟨x, hx⟩ : A), hGbase ⟨x, hx⟩⟩
  · rintro _ ⟨z, rfl⟩
    exact (H (Set.inclusion hAS z.1, z.2)).property
  · intro z
    rw [hG]
    exact hside (Set.inclusion hAS z.1, z.2)

end BrownCollar
