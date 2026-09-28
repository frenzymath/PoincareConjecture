import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] (K : SimplicialComplex 𝕜 E)



def finiteFaceSpan (A : Finset K.faces) : SimplicialComplex 𝕜 E :=
  ofGenerators (Subtype.val '' (A : Set K.faces))
    (by rintro _ ⟨s, _, rfl⟩; exact K.indep s.property)
    (by rintro _ ⟨s, _, rfl⟩ _ ⟨t, _, rfl⟩; exact K.inter_subset_convexHull s.property t.property)




theorem finiteFaceSpan_faces (A : Finset K.faces) (s : Finset E) :
    s ∈ (K.finiteFaceSpan A).faces ↔ s.Nonempty ∧ ∃ t ∈ A, s ⊆ t.val := by
  constructor
  · rintro ⟨hs, _, ⟨t, ht, rfl⟩, hst⟩
    exact ⟨hs, t, ht, hst⟩
  · rintro ⟨hs, t, ht, hst⟩
    exact ⟨hs, t.val, ⟨t, ht, rfl⟩, hst⟩



theorem finiteFaceSpan_le (A : Finset K.faces) : K.finiteFaceSpan A ≤ K := by
  intro s hs
  obtain ⟨hne, t, _, hst⟩ := (K.finiteFaceSpan_faces A s).mp hs
  exact K.down_closed t.property hst hne



theorem finiteFaceSpan_finite (A : Finset K.faces) : (K.finiteFaceSpan A).faces.Finite :=
  finite_ofGenerators_faces (A.finite_toSet.image Subtype.val) _ _



theorem finiteFaceSpan_mono : Monotone K.finiteFaceSpan := by
  intro A B hAB s hs
  change s ∈ (K.finiteFaceSpan A).faces at hs
  change s ∈ (K.finiteFaceSpan B).faces
  rw [K.finiteFaceSpan_faces] at hs ⊢
  obtain ⟨hne, t, ht, hst⟩ := hs
  exact ⟨hne, t, hAB ht, hst⟩



theorem iUnion_finiteFaceSpan_faces :
    (⋃ A : Finset K.faces, (K.finiteFaceSpan A).faces) = K.faces := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨A, hA⟩ := mem_iUnion.mp hs
    exact K.finiteFaceSpan_le A hA
  · intro hs
    refine mem_iUnion.mpr ⟨{⟨s, hs⟩}, ?_⟩
    exact (K.finiteFaceSpan_faces _ _).mpr
      ⟨K.nonempty_of_mem_faces hs, ⟨s, hs⟩, Finset.mem_singleton_self _, Finset.Subset.refl s⟩



theorem iUnion_finiteFaceSpan_space :
    (⋃ A : Finset K.faces, (K.finiteFaceSpan A).space) = K.space := by
  ext x
  constructor
  · intro hx
    obtain ⟨A, hA⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hA
    exact K.convexHull_subset_space (K.finiteFaceSpan_le A hs) hxs
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    rw [← K.iUnion_finiteFaceSpan_faces] at hs
    obtain ⟨A, hA⟩ := mem_iUnion.mp hs
    exact mem_iUnion.mpr ⟨A, mem_space_iff.mpr ⟨s, hA, hxs⟩⟩

end Geometry.SimplicialComplex
