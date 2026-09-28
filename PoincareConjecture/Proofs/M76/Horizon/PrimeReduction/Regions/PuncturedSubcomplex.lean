import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_closed_punctured_subcomplex
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A B : ι → SimplicialComplex ℝ E)
    (hAK : ∀ i, A i ≤ K) (hBK : ∀ i, B i ≤ K)
    (hclosed : IsClosed (K.space \ ⋃ i, (A i).space \ (B i).space)) :
    ∃ L : SimplicialComplex ℝ E, L ≤ K ∧ L.faces.Finite ∧
      L.space = K.space \ ⋃ i, (A i).space \ (B i).space ∧
      ∀ J : SimplicialComplex ℝ E, J ≤ K →
        J.space ⊆ K.space \ ⋃ i, (A i).space \ (B i).space → J ≤ L := by
  let p := K.space \ ⋃ i, (A i).space \ (B i).space
  let L : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ p}
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }
  have hLK : L ≤ K := fun _ hs => hs.1
  have hLp : L.space ⊆ p := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact hs.2 hxs
  refine ⟨L, hLK, hK.subset hLK, hLp.antisymm ?_, ?_⟩
  · rintro x ⟨hxK, hxholes⟩
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
    have hrel : intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ⊆ p := by
      intro y hy
      refine ⟨K.convexHull_subset_space hs (intrinsicInterior_subset hy), ?_⟩
      intro hyholes
      obtain ⟨i, hyA, hyB⟩ := mem_iUnion.mp hyholes
      have hsA := K.face_mem_subcomplex_of_intrinsicInterior (A i) (hAK i) hs hy hyA
      have hxA := (A i).convexHull_subset_space hsA (intrinsicInterior_subset hxs)
      have hxB : x ∈ (B i).space := by
        by_contra hn
        exact hxholes (mem_iUnion.mpr ⟨i, hxA, hn⟩)
      have hsB := K.face_mem_subcomplex_of_intrinsicInterior (B i) (hBK i) hs hxs hxB
      exact hyB ((B i).convexHull_subset_space hsB (intrinsicInterior_subset hy))
    have hface : convexHull ℝ (s : Set E) ⊆ p :=
      (convex_convexHull ℝ (s : Set E)).subset_closure_intrinsicInterior.trans
        (closure_minimal hrel hclosed)
    exact L.convexHull_subset_space ⟨hs, hface⟩ (intrinsicInterior_subset hxs)
  · intro J hJK hJp s hs
    exact ⟨hJK hs, (J.convexHull_subset_space hs).trans hJp⟩

end Geometry.SimplicialComplex
