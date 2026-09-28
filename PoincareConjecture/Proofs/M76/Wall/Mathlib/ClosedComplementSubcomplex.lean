import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_closedComplement_subcomplex
    (K P : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hPK : P ≤ K) :
    ∃ N : SimplicialComplex ℝ E, N ≤ K ∧ N.faces.Finite ∧
      N.space = closure (K.space \ P.space) ∧
      ∀ L : SimplicialComplex ℝ E, L ≤ K →
        L.space ⊆ closure (K.space \ P.space) → L ≤ N := by
  let T := closure (K.space \ P.space)
  let N : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ T}
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }
  have hNK : N ≤ K := fun _ hs => hs.1
  have hN : N.faces.Finite := hK.subset hNK
  have hNT : N.space ⊆ T := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact hs.2 hxs
  have hinside : K.space \ P.space ⊆ N.space := by
    rintro x ⟨hxK, hxP⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxK
    have hsP : s ∉ P.faces := fun hsP => hxP (P.convexHull_subset_space hsP hxs)
    have hrel : intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ⊆ K.space \ P.space := by
      intro y hy
      refine ⟨K.convexHull_subset_space hs (intrinsicInterior_subset hy), ?_⟩
      intro hyP
      obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hyP
      exact hsP (P.down_closed ht
        (K.subset_of_mem_intrinsicInterior_face hs (hPK ht) hy hyt)
        (K.nonempty_of_mem_faces hs))
    have hface : convexHull ℝ (s : Set E) ⊆ T :=
      (convex_convexHull ℝ (s : Set E)).subset_closure_intrinsicInterior.trans
        (closure_mono hrel)
    exact N.convexHull_subset_space ⟨hs, hface⟩ hxs
  refine ⟨N, hNK, hN, hNT.antisymm ?_, ?_⟩
  · exact closure_minimal hinside (N.isCompact_space_of_finite hN).isClosed
  · intro L hLK hLT s hs
    exact ⟨hLK hs, (L.convexHull_subset_space hs).trans hLT⟩

end Geometry.SimplicialComplex
