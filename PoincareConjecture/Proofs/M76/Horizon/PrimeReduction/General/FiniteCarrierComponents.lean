import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions







set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_finite_triangulation_connectedComponentIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (x : E) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧
      J.space = connectedComponentIn K.space x := by
  let C := connectedComponentIn K.space x
  let J : SimplicialComplex ℝ E := {
    faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ C}
    indep := fun hs => K.indep hs.1
    isRelLowerSet_faces := by
      intro s hs
      refine ⟨K.nonempty_of_mem_faces hs.1,?_⟩
      intro t hts ht
      exact ⟨K.down_closed hs.1 hts ht,(convexHull_mono hts).trans hs.2⟩
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }
  refine ⟨J,hK.subset (fun _ hs => hs.1),?_⟩
  apply Subset.antisymm
  · intro y hy
    obtain ⟨s,hs,hys⟩ := SimplicialComplex.mem_space_iff.mp hy
    exact hs.2 hys
  · intro y hy
    obtain ⟨s,hs,hys⟩ := SimplicialComplex.mem_space_iff.mp
      (connectedComponentIn_subset K.space x hy)
    have hsub := (convex_convexHull ℝ (s : Set E)).isPreconnected.subset_connectedComponentIn
      hys (K.convexHull_subset_space hs)
    rw [← connectedComponentIn_eq hy] at hsub
    exact SimplicialComplex.mem_space_iff.mpr ⟨s,⟨hs,hsub⟩,hys⟩

end PoincareConjecture.M76
