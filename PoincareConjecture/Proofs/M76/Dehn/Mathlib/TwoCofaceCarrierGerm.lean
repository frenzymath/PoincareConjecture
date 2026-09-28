import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

theorem exists_open_two_coface_carrier_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s a b : Finset E} (hs : s ∈ K.faces) (ha : a ∈ K.faces) (hb : b ∈ K.faces)
    (hcofaces : ∀ t ∈ K.faces, s ⊆ t → t ⊆ a ∨ t ⊆ b)
    {p : E} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, x ∈ K.space ↔
        x ∈ convexHull ℝ (a : Set E) ∪ convexHull ℝ (b : Set E) := by
  classical
  have hpK : p ∈ K.space := K.convexHull_subset_space hs (intrinsicInterior_subset hp)
  have hstar := K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hs ⟨p, hpK⟩ hp
  obtain ⟨V, hVstar, hV, hpV⟩ := mem_nhds_iff.mp hstar
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have hpU : p ∈ U := hUV.symm.subset hpV
  refine ⟨U, hU, hpU, ?_⟩
  intro x hxU
  constructor
  · intro hxK
    have hxstar : x ∈ (K.closedFaceStar s).space :=
      hVstar (hUV.subset (show (⟨x, hxK⟩ : K.space) ∈ Subtype.val ⁻¹' U from hxU))
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxstar
    have hstK : s ∪ t ∈ K.faces := ht.2
    rcases hcofaces (s ∪ t) hstK Finset.subset_union_left with h | h
    · exact Or.inl (convexHull_mono (Finset.subset_union_right.trans h) hxt)
    · exact Or.inr (convexHull_mono (Finset.subset_union_right.trans h) hxt)
  · rintro (hx | hx)
    · exact K.convexHull_subset_space ha hx
    · exact K.convexHull_subset_space hb hx

end Geometry.SimplicialComplex
