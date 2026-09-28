import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.BarycentricStarCharts
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]




theorem barycentricNeighborhood_two_sides
    (K N P M : SimplicialComplex ℝ E)
    [Fintype K.faces] [Fintype P.faces] [Fintype M.faces] [Finite N.faces]
    (hPK : P ≤ K) (hMK : M ≤ K) (hNP : N ≤ P) (hNM : N ≤ M)
    (hcover : ∀ p ∈ N.vertices, (K.closedStar p).space ⊆ P.space ∪ M.space)
    (hinter : P.space ∩ M.space = N.space) :
    (K.barycentricNeighborhood N).space =
        (P.barycentricNeighborhood N).space ∪ (M.barycentricNeighborhood N).space ∧
      (P.barycentricNeighborhood N).space ∩ (M.barycentricNeighborhood N).space =
        N.space := by
  have hNK : N ≤ K := fun _ ha => hPK (hNP ha)
  constructor
  · rw [K.barycentricNeighborhood_space_eq_iUnion_dualBlocks N,
      P.barycentricNeighborhood_space_eq_iUnion_dualBlocks N,
      M.barycentricNeighborhood_space_eq_iUnion_dualBlocks N]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
      have hpK : p ∈ K.vertices := hNK hp
      have hxstar : x ∈ (K.closedStar p).space := by
        apply K.barycentric_closedStar_space_subset hpK
        rwa [← K.barycentricDualBlock_singleton_eq_closedStar hpK]
      rcases hcover p hp hxstar with hxP | hxM
      · exact Or.inl (mem_iUnion₂.mpr ⟨p, hp,
          (K.barycentricDualBlock_space_inter_subcomplex P hPK {p}).subset ⟨hxp, hxP⟩⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨p, hp,
          (K.barycentricDualBlock_space_inter_subcomplex M hMK {p}).subset ⟨hxp, hxM⟩⟩)
    · intro x hx
      rcases hx with hxP | hxM
      · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxP
        exact mem_iUnion₂.mpr ⟨p, hp,
          space_subset_of_le (K.barycentricDualBlock_mono_of_subcomplex P hPK {p}) hxp⟩
      · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxM
        exact mem_iUnion₂.mpr ⟨p, hp,
          space_subset_of_le (K.barycentricDualBlock_mono_of_subcomplex M hMK {p}) hxp⟩
  · apply Subset.antisymm
    · rintro x ⟨hxP, hxM⟩
      apply hinter.subset
      exact ⟨P.barycentricSubdivision_isSubdivision.space_eq.subset
          (space_subset_of_le (P.barycentricNeighborhood_le N) hxP),
        M.barycentricSubdivision_isSubdivision.space_eq.subset
          (space_subset_of_le (M.barycentricNeighborhood_le N) hxM)⟩
    · intro x hx
      exact ⟨P.space_subset_barycentricNeighborhood hNP hx,
        M.space_subset_barycentricNeighborhood hNM hx⟩

end Geometry.SimplicialComplex
