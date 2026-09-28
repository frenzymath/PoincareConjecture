import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import Mathlib.Data.Finset.Max










set_option autoImplicit false

open Set Geometry





theorem Set.Finite.exists_pos_lt_positive_values {ι : Type*} {s : Set ι}
    (hs : s.Finite) (f : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ β : ℝ, β ∈ Ioo 0 δ ∧ ∀ i ∈ s, 0 < f i → β < f i := by
  classical
  let t : Finset ℝ := insert δ ((hs.toFinset.image f).filter (0 < ·))
  have ht : t.Nonempty := ⟨δ, Finset.mem_insert_self _ _⟩
  have hpos : ∀ x ∈ t, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hδ
    · exact (Finset.mem_filter.mp hx).2
  have hm : 0 < t.min' ht := hpos _ (t.min'_mem ht)
  refine ⟨t.min' ht / 2, ⟨half_pos hm, ?_⟩, fun i hi hfi => ?_⟩
  · exact (half_lt_self hm).trans_le (t.min'_le δ (Finset.mem_insert_self _ _))
  · apply (half_lt_self hm).trans_le
    exact t.min'_le (f i) (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i, hs.mem_toFinset.mpr hi, rfl⟩, hfi⟩))

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_singleVertex_slab_width (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) {q : E}
    (hzero : ∀ z ∈ K.vertices, A z = 0 → z = q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ β : ℝ, β ∈ Ioo 0 δ ∧ ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z := by
  obtain ⟨β, hβ, hgap⟩ :=
    (K.finite_vertices_of_finite_faces hK).exists_pos_lt_positive_values A hδ
  refine ⟨β, hβ, fun z hz hzq => ?_⟩
  have hAz : A z ≠ 0 := fun h => hzq (hzero z hz h)
  rcases lt_or_gt_of_ne hAz with hneg | hpos
  · exact Or.inl hneg
  · exact Or.inr (hgap z hz hpos)

end Geometry.SimplicialComplex
