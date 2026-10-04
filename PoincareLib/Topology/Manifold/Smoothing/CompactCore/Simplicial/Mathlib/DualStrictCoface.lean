import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricDualSubcomplex

/-!
# Complete coface duals lie in the whole centroid link

A strict coface excludes the smaller face's centroid from every
simplex of its dual. The smaller dual is its centroid's entire
closed star, so this gives literal link containment for whole joint
disks. See Wall013, section 4, Hudson 1969, pp. 8--9, 58--63.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

/-- The whole dual block of a strict coface is a subcomplex of
the smaller face's entire centroid link. In particular a joint
disk lies in each neighboring vertex block's complete boundary.
See Wall013, section 4. -/
theorem barycentricDualBlock_le_link_of_ssubset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {s t : Finset E} (hs : s ∈ K.faces) (hst : s ⊂ t) :
    K.barycentricDualBlock t ≤ (K.barycentricDualBlock s).link (s.centroid ℝ id) := by
  intro f hf
  have hsf := K.barycentricDualBlock_antitone hst.le hf
  have hjoin : f ∈ ((K.barycentricDualBlock s).closedStar (s.centroid ℝ id)).faces := by
    rw [K.barycentricDualBlock_closedStar_faceCentroid hs]
    exact hsf
  refine ⟨hsf, ?_, hjoin.2⟩
  intro hcenter
  obtain ⟨u, hu, htu, huc⟩ := hf.2 (s.centroid ℝ id) hcenter
  have heq : (⟨u, hu⟩ : K.faces) = ⟨s, hs⟩ := K.faceCentroid_injective huc
  have hus : u = s := congrArg Subtype.val heq
  have hts : t ⊆ s := hus ▸ htu
  exact hst.ne (Finset.Subset.antisymm hst.le hts)

end Geometry.SimplicialComplex
