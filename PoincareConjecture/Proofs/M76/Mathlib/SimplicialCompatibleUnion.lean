import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E]




theorem cross_inter_subset_of_common_face (C D : SimplicialComplex K E)
    (d : Finset E) (hdC : d ∈ C.faces) (hdD : d ∈ D.faces)
    (hinter : C.space ∩ D.space ⊆ convexHull K (d : Set E))
    {s t : Finset E} (hs : s ∈ C.faces) (ht : t ∈ D.faces) :
    convexHull K (s : Set E) ∩ convexHull K (t : Set E) ⊆
      convexHull K ((s : Set E) ∩ t) := by
  classical
  rintro x ⟨hxs, hxt⟩
  have hxd := hinter ⟨C.convexHull_subset_space hs hxs, D.convexHull_subset_space ht hxt⟩
  have hsd := C.inter_subset_convexHull hs hdC ⟨hxs, hxd⟩
  have htd := D.inter_subset_convexHull ht hdD ⟨hxt, hxd⟩
  have heq := (C.indep hdC).convexHull_inter
    (t₁ := s ∩ d) (t₂ := t ∩ d) Finset.inter_subset_right Finset.inter_subset_right
  simp only [Finset.coe_inter] at heq
  have hx : x ∈ convexHull K (((s : Set E) ∩ d) ∩ ((t : Set E) ∩ d)) := by
    rw [heq]
    exact ⟨hsd, htd⟩
  have hsub : (((s : Set E) ∩ d) ∩ ((t : Set E) ∩ d)) ⊆ (s : Set E) ∩ t :=
    fun _ h => ⟨h.1.1, h.2.1⟩
  exact convexHull_mono hsub hx

omit [IsStrictOrderedRing K]




def unionOfCompatible (C D : SimplicialComplex K E)
    (hcross : ∀ s ∈ C.faces, ∀ t ∈ D.faces,
      convexHull K (s : Set E) ∩ convexHull K (t : Set E) ⊆
        convexHull K ((s : Set E) ∩ t)) : SimplicialComplex K E where
  faces := C.faces ∪ D.faces
  isRelLowerSet_faces := by
    rintro s (hs | hs)
    · exact ⟨C.nonempty_of_mem_faces hs, fun t hts ht => Or.inl (C.down_closed hs hts ht)⟩
    · exact ⟨D.nonempty_of_mem_faces hs, fun t hts ht => Or.inr (D.down_closed hs hts ht)⟩
  indep := by
    rintro s (hs | hs)
    · exact C.indep hs
    · exact D.indep hs
  inter_subset_convexHull := by
    rintro s t (hs | hs) (ht | ht)
    · exact C.inter_subset_convexHull hs ht
    · exact hcross s hs t ht
    · simpa only [inter_comm] using hcross t ht s hs
    · exact D.inter_subset_convexHull hs ht

variable (C D : SimplicialComplex K E)
  (hcross : ∀ s ∈ C.faces, ∀ t ∈ D.faces,
    convexHull K (s : Set E) ∩ convexHull K (t : Set E) ⊆
      convexHull K ((s : Set E) ∩ t))



theorem faces_unionOfCompatible : (C.unionOfCompatible D hcross).faces = C.faces ∪ D.faces := rfl



theorem space_unionOfCompatible : (C.unionOfCompatible D hcross).space = C.space ∪ D.space := by
  ext x
  simp only [mem_space_iff, faces_unionOfCompatible, mem_union]
  aesop



theorem vertices_unionOfCompatible :
    (C.unionOfCompatible D hcross).vertices = C.vertices ∪ D.vertices := rfl



theorem finite_faces_unionOfCompatible (hC : C.faces.Finite) (hD : D.faces.Finite) :
    (C.unionOfCompatible D hcross).faces.Finite := hC.union hD

end Geometry.SimplicialComplex
