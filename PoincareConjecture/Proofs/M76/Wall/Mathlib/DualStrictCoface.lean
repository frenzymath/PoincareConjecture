import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

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
