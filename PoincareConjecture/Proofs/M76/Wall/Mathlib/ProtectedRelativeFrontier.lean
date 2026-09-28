import PoincareConjecture.Proofs.M76.Wall.Mathlib.RelativeFilledFrontier

set_option autoImplicit false

open Set

namespace Set

theorem protected_relative_frontier_eq_of_frontier
    {X : Type*} [TopologicalSpace X] {R K F : Set X}
    (hR : IsClosed R) (hK : IsClosed K) (hKR : K ⊆ R)
    (hF : F ⊆ interior R)
    (hprotect : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (hfront : frontier K = frontier R ∪ F) :
    frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' F := by
  ext x
  constructor
  · intro hx
    have hxK : (x : X) ∈ K := (hK.preimage continuous_subtype_val).frontier_subset hx
    have hxR : (x : X) ∈ interior R := by
      by_contra hnot
      have hxB : (x : X) ∈ frontier R := by
        rw [hR.frontier_eq]
        exact ⟨hKR hxK, hnot⟩
      exact hx.2 (hprotect hxB)
    have hxfront : (x : X) ∈ frontier K :=
      ⟨subset_closure hxK, fun hi => hx.2
        (preimage_interior_subset_interior_preimage continuous_subtype_val hi)⟩
    rcases hfront.subset hxfront with hxB | hxF
    · exact False.elim (hxB.2 hxR)
    · exact hxF
  · intro hxF
    have hxfront : (x : X) ∈ frontier K := hfront.symm.subset (Or.inr hxF)
    rw [(hK.preimage continuous_subtype_val).frontier_eq]
    refine ⟨hK.frontier_subset hxfront, ?_⟩
    intro hi
    exact hxfront.2 ((mem_interior_subtype_preimage_iff_of_mem_interior x (hF hxF)).mp hi)

end Set
