import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection











set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem HasAlexanderCurvePresentation.hasDisjointPolygonPresentation_of_nonisolated
    {S : Set E} (h : HasAlexanderCurvePresentation S 0)
    (hacc : ∀ x ∈ S, x ∈ closure (S \ {x})) :
    HasDisjointPolygonPresentation S := by
  obtain ⟨m, n, P, r, hP, hr, hcover, _, hcount⟩ := h
  have hpair := (alexanderCurveCount_eq_zero_iff (fun i => (P i).boundary ℝ)).mp hcount
  have hclosed : IsClosed (⋃ i, (P i).boundary ℝ) :=
    isClosed_iUnion_of_finite (fun i => (P i).isClosed_boundary)
  refine ⟨m, n, P, hP, ?_, hpair⟩
  apply Subset.antisymm
  · intro x hx
    by_contra hnot
    have hxr : x ∈ r := (hcover.subset hx).resolve_right hnot
    have hrx : r = {x} := hr.eq_singleton_of_mem hxr
    have hsub : S \ {x} ⊆ ⋃ i, (P i).boundary ℝ := by
      intro y hy
      rcases hcover.subset hy.1 with hyr | hyP
      · exact (hy.2 (hrx ▸ hyr)).elim
      · exact hyP
    exact hnot (closure_minimal hsub hclosed (hacc x hx))
  · exact fun x hx => hcover.symm.subset (Or.inr hx)

end Set
