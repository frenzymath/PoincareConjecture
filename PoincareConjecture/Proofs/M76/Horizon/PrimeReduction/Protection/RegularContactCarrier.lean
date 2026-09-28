import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion

set_option autoImplicit false
open Set Geometry

namespace Set

theorem HasDisjointPolygonPresentation.exists_finite_contact_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (h : HasDisjointPolygonPresentation S) :
    ∃ G : SimplicialComplex ℝ E, G.faces.Finite ∧ G.space = S := by
  classical
  obtain ⟨m,n,P,hP,hcover,hpair⟩ := h
  let C (i : Fin m) := (P i).simplicialComplex (hP i).2
  have hCs (i : Fin m) : (C i).space = (P i).boundary ℝ :=
    (P i).simplicialComplex_space (hP i).2
  have hcross : ∀ i j, ∀ s ∈ (C i).faces, ∀ t ∈ (C j).faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
    intro i j s hs t ht
    by_cases hij : i = j
    · subst j
      exact (C i).inter_subset_convexHull hs ht
    · rintro x ⟨hxs,hxt⟩
      exact (disjoint_left.mp (hpair hij)
        ((hCs i).subset ((C i).convexHull_subset_space hs hxs))
        ((hCs j).subset ((C j).convexHull_subset_space ht hxt))).elim
  refine ⟨SimplicialComplex.iUnionOfCompatible C hcross,
    SimplicialComplex.finite_faces_iUnionOfCompatible C hcross
      (fun i => (P i).finite_simplicialComplex_faces (hP i).2),?_⟩
  rw [SimplicialComplex.space_iUnionOfCompatible]
  exact (iUnion_congr hCs).trans hcover.symm

end Set
