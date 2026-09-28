import PoincareConjecture.Proofs.M76.Mathlib.ConicalStar



set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]


theorem mem_coneAtZero_faces_cases (K : SimplicialComplex ℝ E)
    (hlin : ∀ t ∈ K.faces, LinearIndependent ℝ ((↑) : t → E))
    (hrad : InjOn (NormedSpace.normalize : E → E) K.space) (s : Finset E) :
    s ∈ (K.coneAtZero hlin hrad).faces ↔
      s ∈ K.faces ∨ s = {0} ∨ ∃ t ∈ K.faces, s = insert 0 t := by
  constructor
  · intro hs
    by_cases hz : (0 : E) ∈ s
    · rcases hs.2 with h | h
      · right; left
        simpa only [h, Finset.insert_empty] using (Finset.insert_erase hz).symm
      · exact Or.inr (Or.inr ⟨s.erase 0, h, (Finset.insert_erase hz).symm⟩)
    · left
      have h := hs.2
      rw [Finset.erase_eq_of_notMem hz] at h
      exact h.resolve_left hs.1.ne_empty
  · rintro (hs | rfl | ⟨t, ht, rfl⟩)
    · exact K.le_coneAtZero hlin hrad hs
    · exact K.zero_mem_coneAtZero_vertices hlin hrad
    · exact insert_zero_mem_coneAtZero_faces hlin hrad ht

end Geometry.SimplicialComplex
