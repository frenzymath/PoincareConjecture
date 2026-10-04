import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FullSimplexBasis
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplexIntrinsicFrontier
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplexRelativeInteriorCoordinates
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# The actual boundaries and centers of planar source triangles

The original independent three-point face supplies its interior centroid
and its exact boundary edges. Distinct triangles meet only in their
boundaries, so fixed boundary programs agree on all face overlaps.
See Wall005, construction step 2, and Hudson, pp. 15--19.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

/-- Removing one original vertex of a triangle gives an actual original
edge, retaining its two remaining vertices. -/
theorem triangle_erase_is_edge (K : SimplicialComplex ℝ E)
    {t : Finset E} (ht : t ∈ K.faces) (hcard : t.card = 3) {p : E} (hp : p ∈ t) :
    t.erase p ∈ K.faces ∧ (t.erase p).card = 2 ∧ t.erase p ⊆ t := by
  have hc : (t.erase p).card = 2 := by rw [Finset.card_erase_of_mem hp, hcard]
  exact ⟨K.down_closed ht (Finset.erase_subset p t)
    (Finset.card_pos.mp (by omega)), hc, Finset.erase_subset p t⟩

omit [DecidableEq E] in
/-- The centroid of the actual planar triangle is an ambient interior
point, derived from its original independent vertex set. -/
theorem triangle_centroid_mem_interior [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 2)
    {t : Finset E} (ht : t ∈ K.faces) (hcard : t.card = 3) :
    t.centroid ℝ id ∈ interior (convexHull ℝ (t : Set E)) := by
  let b := (K.indep ht).affineBasisOfCard (by omega : t.card = Module.finrank ℝ E + 1)
  have hc := b.centroid_mem_interior_convexHull
  change Finset.univ.centroid ℝ ((↑) : t → E) ∈ interior (convexHull ℝ (range b)) at hc
  simpa only [Finset.centroid_univ, b, AffineIndependent.range_affineBasisOfCard] using hc

/-- The complete frontier of a planar triangle is the union of its three
literal erased-vertex edge hulls. -/
theorem triangle_frontier_eq_iUnion_erase [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 2)
    {t : Finset E} (ht : t ∈ K.faces) (hcard : t.card = 3) :
    frontier (convexHull ℝ (t : Set E)) =
      ⋃ p : t, convexHull ℝ ((t.erase p : Finset E) : Set E) := by
  let b := (K.indep ht).affineBasisOfCard (by omega : t.card = Module.finrank ℝ E + 1)
  have hi : intrinsicInterior ℝ (convexHull ℝ (t : Set E)) =
      interior (convexHull ℝ (t : Set E)) := by
    apply Subset.antisymm _ interior_subset_intrinsicInterior
    intro x hx
    have hb := b.mem_interior_convexHull_of_mem_intrinsicInterior (by simpa [b] using hx)
    simpa [b] using hb
  have hfront : intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
      frontier (convexHull ℝ (t : Set E)) := by
    rw [← closure_sdiff_intrinsicInterior, hi, frontier]
  rw [← hfront]
  ext x
  rw [AffineIndependent.mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces ht) (K.indep ht) x]
  simp only [mem_iUnion, Subtype.exists, exists_prop]

/-- All source-region data for an actual planar triangle, including its
chosen centroid and every original boundary edge, are constructed. -/
theorem planar_triangle_geometry [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 2)
    {t : Finset E} (ht : t ∈ K.faces) (hcard : t.card = 3) :
    IsCompact (convexHull ℝ (t : Set E)) ∧ Convex ℝ (convexHull ℝ (t : Set E)) ∧
      t.centroid ℝ id ∈ interior (convexHull ℝ (t : Set E)) ∧
      frontier (convexHull ℝ (t : Set E)) =
        ⋃ p : t, convexHull ℝ ((t.erase p : Finset E) : Set E) ∧
      ∀ p ∈ t, t.erase p ∈ K.faces ∧ (t.erase p).card = 2 ∧ t.erase p ⊆ t := by
  exact ⟨t.finite_toSet.isCompact_convexHull ℝ, convex_convexHull ℝ _,
    K.triangle_centroid_mem_interior hdim ht hcard,
    K.triangle_frontier_eq_iUnion_erase hdim ht hcard,
    fun _ hp => K.triangle_erase_is_edge ht hcard hp⟩

/-- Distinct actual triangles meet inside both complete frontiers. This
intersection statement does not require a planar ambient space. -/
theorem distinct_triangle_inter_subset_frontiers (K : SimplicialComplex ℝ E)
    {t u : Finset E} (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htcard : t.card = 3) (hucard : u.card = 3) (hne : t ≠ u) :
    convexHull ℝ (t : Set E) ∩ convexHull ℝ (u : Set E) ⊆
      frontier (convexHull ℝ (t : Set E)) ∩ frontier (convexHull ℝ (u : Set E)) := by
  have htu : t ∩ u ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, by
    intro h
    have hsub : t ⊆ u := h ▸ Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))⟩
  have hut : t ∩ u ⊂ u := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, by
    intro h
    have hsub : u ⊆ t := h ▸ Finset.inter_subset_left
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm⟩
  intro x hx
  have hxi : x ∈ convexHull ℝ ((t ∩ u : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull ht hu hx
  exact ⟨intrinsicFrontier_subset_frontier ((K.indep ht).convexHull_subset_intrinsicFrontier htu hxi),
    intrinsicFrontier_subset_frontier ((K.indep hu).convexHull_subset_intrinsicFrontier hut hxi)⟩

end Geometry.SimplicialComplex
