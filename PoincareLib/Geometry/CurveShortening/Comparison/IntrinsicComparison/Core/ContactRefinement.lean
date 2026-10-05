import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Child.Compatibility

/-! Mesh subdivisions retain actual parent triangles and their coordinate contacts.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareMT.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareMT

/-- Every actual triangle of a subdividing mesh lies in an original mesh triangle. Source:
Morgan--Tian Proposition 19.35, printed pp. 467-481, especially the regional Gauss--Bonnet
argument of Lemma 19.45, p. 474; the explicit coordinate construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-contacts.md`, Mathematical Checks. -/
theorem m64Intrinsic_mesh_subdivision_triangle_parent
    {S T : TriangleMesh} (hST : S.toPlaneComplex.Subdivides T.toPlaneComplex)
    (s : S.Triangle) :
    ∃ t : T.Triangle,
      convexHull ℝ (range (meshTriangleBasis S s)) ⊆
        convexHull ℝ (range (meshTriangleBasis T t)) := by
  have hs : s.1 ∈ S.toPlaneComplex.simplexes := S.mem_faces_iff.mpr
    ⟨Finset.card_pos.mp (by rw [S.card_triangle _ s.2]; omega), s.1, s.2, subset_rfl⟩
  obtain ⟨q, hq, hsq⟩ := hST.2 s.1 hs
  obtain ⟨_, t, ht, hqt⟩ := T.mem_faces_iff.mp hq
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [range_meshTriangleBasis, range_meshTriangleBasis]
  exact hsq.trans (convexHull_mono (image_mono hqt))

/-- Actual mesh subdivision preserves the original canonical coordinate-boundary contact.
Source: Morgan--Tian Proposition 19.35, printed pp. 467-481, especially the regional
Gauss--Bonnet argument of Lemma 19.45, p. 474; the explicit coordinate construction is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-contacts.md`,
Mathematical Checks. -/
theorem m64Intrinsic_mesh_subdivision_preserves_boundary_contact
    {S T : TriangleMesh} (hST : S.toPlaneComplex.Subdivides T.toPlaneComplex)
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (hcontact : ∀ t : T.Triangle, CoordinateTriangleBoundaryIntersection
      (OpenPartialHomeomorph.refl AnnulusCoordinates) F (meshTriangleBasis T t) b) :
    ∀ s : S.Triangle, CoordinateTriangleBoundaryIntersection
      (OpenPartialHomeomorph.refl AnnulusCoordinates) F (meshTriangleBasis S s) b := by
  intro s
  obtain ⟨t, ht⟩ := m64Intrinsic_mesh_subdivision_triangle_parent hST s
  exact m64Intrinsic_canonical_contact_children _ F (meshTriangleBasis T t) b
    (meshTriangleBasis S s) b (subset_univ _) hsource ht (Subset.refl _) (hcontact t)

end PoincareMT
