import PoincareConjecture.Proofs.M76.Mathlib.RadialRealizationCones

set_option autoImplicit false

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

theorem RadialEmbedding.cone_space (v : A.RadialEmbedding E) :
    v.cone.space = ⋃ s ∈ insert ∅ A.faces,
      convexHull ℝ (insert 0 (v.val '' (s : Set ι))) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
    have ht' : t.Nonempty ∧ (t.erase 0 = ∅ ∨ t.erase 0 ∈ v.complex.faces) := ht
    have hsub : (t : Set E) ⊆ insert 0 (t.erase 0 : Set E) := by
      simpa only [Finset.coe_insert] using
        (show (t : Set E) ⊆ (insert 0 (t.erase 0) : Finset E) from
          Finset.insert_erase_subset _ _)
    rcases ht'.2 with he | he
    · refine mem_iUnion₂.mpr ⟨∅, mem_insert _ _, ?_⟩
      have h := convexHull_mono hsub hxt
      simpa only [he, Finset.coe_empty, Set.image_empty] using h
    · rw [v.complex_faces] at he
      obtain ⟨s, hs, hts⟩ := he
      exact mem_iUnion₂.mpr ⟨s, mem_insert_of_mem _ hs,
        convexHull_mono (hts ▸ hsub) hxt⟩
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    rcases hs with rfl | hs
    · have hx0 : x = 0 := by simpa using hxs
      subst x
      exact SimplicialComplex.vertices_subset_space
        (SimplicialComplex.zero_mem_coneAtZero_vertices
          v.complex_linearIndependent v.complex_injOn_normalize)
    · have hface : s.image v.val ∈ v.complex.faces := by
        rw [v.complex_faces_image]
        exact mem_image_of_mem _ hs
      have hcone := SimplicialComplex.insert_zero_mem_coneAtZero_faces
        v.complex_linearIndependent v.complex_injOn_normalize hface
      apply SimplicialComplex.convexHull_subset_space hcone
      simpa only [Finset.coe_insert, Finset.coe_image] using hxs

end AbstractSimplicialComplex
