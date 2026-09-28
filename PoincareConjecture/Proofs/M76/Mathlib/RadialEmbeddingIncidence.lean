import PoincareConjecture.Proofs.M76.Mathlib.RadialEmbeddingSpace










set_option autoImplicit false

open Set Geometry NormedSpace

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι} {v : ι → E}



theorem IsRadialEmbedding.linearIndependent_face_image (hv : A.IsRadialEmbedding v)
    {s : Finset ι} (hs : s ∈ A.faces) :
    LinearIndependent ℝ ((↑) : ↥(v '' (s : Set ι)) → E) := by
  classical
  obtain ⟨L, hfaces, hlin, _⟩ := hv.2
  have hsi : s.image v ∈ L.faces := by
    rw [hfaces]
    exact ⟨s, hs, Finset.coe_image⟩
  have h : LinearIndependent ℝ ((↑) : ↥(s.image v : Set E) → E) := hlin _ hsi
  rwa [Finset.coe_image] at h




theorem IsRadialEmbedding.vertex_mem_normalize_face_iff (hv : A.IsRadialEmbedding v)
    {s : Finset ι} (hs : s ∈ A.faces) (i : ι) :
    NormedSpace.normalize (v i) ∈ NormedSpace.normalize '' convexHull ℝ (v '' (s : Set ι)) ↔
      i ∈ s := by
  classical
  obtain ⟨L, hfaces, _, hinj⟩ := hv.2
  have hsi : s.image v ∈ L.faces := by
    rw [hfaces]
    exact ⟨s, hs, Finset.coe_image⟩
  have hvi : v i ∈ L.vertices := by
    change {v i} ∈ L.faces
    rw [hfaces]
    exact ⟨{i}, A.singleton_mem i, by simp⟩
  constructor
  · rintro ⟨x, hx, hxi⟩
    have hxs : x ∈ convexHull ℝ (s.image v : Set E) := by
      simpa only [Finset.coe_image] using hx
    have hix : v i = x := hinj (L.vertices_subset_space hvi)
      (SimplicialComplex.convexHull_subset_space hsi hxs) hxi.symm
    have himem := (L.vertex_mem_convexHull_iff hvi hsi).mp (hix ▸ hxs)
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp himem
    exact hv.1 hji ▸ hj
  · intro hi
    exact ⟨v i, subset_convexHull ℝ _ ⟨i, hi, rfl⟩, rfl⟩

end AbstractSimplicialComplex
