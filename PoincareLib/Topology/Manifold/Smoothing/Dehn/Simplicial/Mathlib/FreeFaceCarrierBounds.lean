import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.ClosedStarProjectionCoverage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionIntrinsicDensity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexFiniteAffineCover

/-!
# Bound produced free faces using their actual complete carriers

A face outside the protected subcomplex has its intrinsic interior
outside that entire carrier. If the remaining carrier lies in a closed
active image, density puts the whole free face in that image. A finite
affine cover then gives the actual source-face cardinality bound.
See Hudson1969, Lemma4.6, and Dehn032, section6.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- If the full carrier is covered by a subcomplex and a closed
active set, every face outside that subcomplex lies wholly in the
active set. No purity or fullness premise is needed.
See Dehn032, section6. -/
theorem free_face_hull_subset_closed_active
    (K P : SimplicialComplex ℝ E) (hPK : P ≤ K)
    {C : Set E} (hC : IsClosed C) (hcover : K.space ⊆ P.space ∪ C)
    {a : Finset E} (ha : a ∈ K.faces) (haP : a ∉ P.faces) :
    convexHull ℝ (a : Set E) ⊆ C := by
  have hrel : intrinsicInterior ℝ (convexHull ℝ (a : Set E)) ⊆ C := by
    intro x hx
    rcases hcover (K.convexHull_subset_space ha (intrinsicInterior_subset hx)) with hxP | hxC
    · obtain ⟨b, hb, hxb⟩ := mem_space_iff.mp hxP
      exact False.elim (haP (P.down_closed hb
        (K.subset_of_mem_intrinsicInterior_face ha (hPK hb) hx hxb)
        (K.nonempty_of_mem_faces ha)))
    · exact hxC
  exact (convex_convexHull ℝ (a : Set E)).subset_closure_intrinsicInterior.trans
    (closure_minimal hrel hC)

/-- A whole simplex contained in a finite complex has cardinality
bounded by the largest face of that actual complex. The finite affine
cover argument works inside the simplex's own affine span.
See Dehn032, section6. -/
theorem face_card_le_of_hull_subset_finite_carrier
    (K L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    {a : Finset E} (ha : a ∈ K.faces)
    (hsub : convexHull ℝ (a : Set E) ⊆ L.space)
    {n : ℕ} (hbound : ∀ b ∈ L.faces, b.card ≤ n) : a.card ≤ n := by
  let : Finite L.faces := hL.to_subtype
  have hcover : convexHull ℝ (a : Set E) ⊆
      ⋃ b : L.faces, (affineSpan ℝ (b.val : Set E) : Set E) := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := mem_space_iff.mp (hsub hx)
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, convexHull_subset_affineSpan (s := (b : Set E)) hxb⟩
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ha
  have hne : (convexHull ℝ (a : Set E)).Nonempty :=
    ⟨v, subset_convexHull ℝ (a : Set E) hv⟩
  obtain ⟨b, hb⟩ := Convex.exists_subset_affineSubspace_of_subset_iUnion
    (convex_convexHull ℝ (a : Set E)) hne
    (fun b : L.faces => affineSpan ℝ (b.val : Set E)) hcover
  exact ((K.indep ha).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ (a : Set E)).trans hb)).trans (hbound b.val b.property)

end Geometry.SimplicialComplex
