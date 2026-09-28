import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChildCompatibility








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture





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

end PoincareConjecture
