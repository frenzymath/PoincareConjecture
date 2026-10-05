import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IntrinsicRegularSection

/-!
# A nonisolated zero-charge section has no separate residue

The finite polygon union is closed. A subsingleton residue
outside it would be isolated in the complete section, so every
residue point is absorbed into that polygon union. Zero charge
gives the actual disjointness. See Alexander 1924, pp. 6--8 and
M76 derivation 269.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A complete zero-charge section with no isolated points
is exactly its finite disjoint polygon union. Residue points
already on a polygon are allowed, and the empty section is
included. See Alexander pp. 6--8 and M76 derivation 269. -/
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
