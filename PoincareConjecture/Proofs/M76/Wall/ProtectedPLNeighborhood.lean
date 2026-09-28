import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLHalfspaceNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_protected_PL_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X}
    (hR : PLDomain e R) (hB : IsCompact (frontier R))
    {A : Set X} (hA : IsCompact A) (hAR : A ⊆ R) :
    ∃ K S : Set X, IsCompact K ∧ A ⊆ K ∧ K ⊆ R ∧ PLDomain e K ∧
      IsCompact S ∧ S ⊆ interior R ∧ Disjoint (frontier R) S ∧
      frontier K = frontier R ∪ S ∧
      (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
        interior ((Subtype.val : R → X) ⁻¹' K) ∧
      frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' S := by
  let := ChartedSpace.ofChartCover e hR.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  obtain ⟨P, hP, hAP, _, hhalf⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e hR.compatible
      hR.cover (hA.union hB) isOpen_univ (subset_univ _)
  have hPi : PLDomain e P := ⟨hR.cover, hR.compatible, hP.isClosed, hhalf⟩
  have hBP : frontier R ⊆ interior P := fun _ hx => hAP (Or.inr hx)
  let K : Set X := P ∩ R
  let S : Set X := frontier P ∩ R
  have hS : IsCompact S :=
    (hP.of_isClosed_subset isClosed_frontier hP.isClosed.frontier_subset).inter_right hR.closed
  have hpreK : (Subtype.val : R → X) ⁻¹' K = (Subtype.val : R → X) ⁻¹' P := by
    ext x
    exact and_iff_left x.property
  refine ⟨K, S, hP.inter_right hR.closed, ?_, inter_subset_right,
    hPi.inter_of_frontier_subset_interior hR hBP, hS,
    Set.frontier_inter_subset_interior_of_frontier_subset_interior hBP,
    Set.disjoint_frontier_inter_of_frontier_subset_interior hBP,
    Set.frontier_inter_of_frontier_subset_interior hP.isClosed hR.closed hBP, ?_, ?_⟩
  · intro x hx
    exact ⟨interior_subset (hAP (Or.inl hx)), hAR hx⟩
  · rw [hpreK, Set.interior_subtype_preimage_of_frontier_subset_interior hBP]
    intro x hx
    exact hAP hx
  · rw [hpreK, Set.frontier_subtype_preimage_of_frontier_subset_interior hP.isClosed hBP]
    ext x
    exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩

end PoincareConjecture.M76
