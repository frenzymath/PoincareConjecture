import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Band.Compatibility
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Child.Compatibility
import PoincareLib.Topology.Surface.Triangulation.Regions.Collars.CoreIntersections

/-!
# Canonical contacts for the actual retained band chain

The adjacent cuts and separated nonadjacent bands determine every parent
face contact. Arbitrary actual mesh children preserve these contacts,
including children of the same parent. This prepares the finite regional
subdivision for Morgan--Tian Lemma 19.45, printed p. 474.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareMT

/-- The geometric adjacency and separation of a retained band chain produce canonical
contacts for all distinct constituent faces. Source: Morgan--Tian Proposition 19.35, printed
pp. 467-481, especially the regional Gauss--Bonnet argument of Lemma 19.45, p. 474; the
explicit coordinate construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-contacts.md`, Mathematical Checks. -/
theorem m64Intrinsic_band_chain_faces_canonical
    {n : ℕ} (F : Fin n → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (lo : Fin n → ℝ → ℝ) (a b ua wa ub wb ra rb : Fin n → ℝ)
    (B : ∀ i, ObliqueBandFaces (F i) (lo i) (a i) (b i)
      (ua i) (wa i) (ub i) (wb i) (ra i) (rb i))
    (cut : Fin (n + 1) → Set AnnulusCoordinates)
    (hleft : ∀ i, (B i).leftCut = cut i.castSucc)
    (hright : ∀ i, (B i).rightCut = cut i.succ)
    (hsep : ∀ i j : Fin n, i.succ < j.castSucc → Disjoint (B i).carrier (B j).carrier)
    (hadj : ∀ i j : Fin n, i.succ = j.castSucc →
      (B i).carrier ∩ (B j).carrier = cut i.succ) :
    ∀ (p q : (i : Fin n) × (Fin (B i).interface.count × Bool)), p ≠ q →
      CoordinateTriangleBoundaryIntersection
        ((B p.1).faceCoordinates p.2) ((B q.1).faceCoordinates q.2)
        ((B p.1).faceBasis p.2) ((B q.1).faceBasis q.2) := by
  have hordered (i j : Fin n) (hij : i < j)
      (p : Fin (B i).interface.count × Bool) (q : Fin (B j).interface.count × Bool) :
      CoordinateTriangleBoundaryIntersection ((B i).faceCoordinates p)
        ((B j).faceCoordinates q) ((B i).faceBasis p) ((B j).faceBasis q) := by
    by_cases hnext : i.succ = j.castSucc
    · apply m64Intrinsic_shared_cut_bands_canonical_compatibility (B i) (B j) true false
      · simpa [(B i).endpointEdge_image, hright] using hadj i j hnext
      · simp [(B i).endpointEdge_image, (B j).endpointEdge_image, hright, hleft, hnext]
    · have hgap : i.succ < j.castSucc := by
        apply Fin.mk_lt_mk.mpr
        have hlt : i.val < j.val := hij
        have hne : i.val + 1 ≠ j.val := fun h => hnext (Fin.ext h)
        omega
      apply CoordinateTriangleBoundaryIntersection.disjoint
      rw [← (B i).face_carrier_eq_coordinates, ← (B j).face_carrier_eq_coordinates]
      exact (hsep i j hgap).mono (fun _ hx => mem_iUnion.mpr ⟨p, hx⟩)
        (fun _ hx => mem_iUnion.mpr ⟨q, hx⟩)
  rintro ⟨i, p⟩ ⟨j, q⟩ hpq
  by_cases hij : i = j
  · subst j
    exact m64Intrinsic_band_faces_canonical_compatibility (B i) p q
      (fun h => hpq (h ▸ rfl))
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hordered i j hlt p q
    · exact (hordered j i hgt q p).symm

/-- A family of actual planar subdivisions retains canonical contacts between all distinct
children. Its complete support is unchanged. Source: Morgan--Tian Proposition 19.35, printed
pp. 467-481, especially the regional Gauss--Bonnet argument of Lemma 19.45, p. 474; the
explicit coordinate construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-contacts.md`, Mathematical Checks. -/
theorem m64Intrinsic_coordinate_mesh_family_canonical
    {I : Type*} (F : I → OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j))
    (M : I → TriangleMesh)
    (hsupport : ∀ i, (M i).toPlaneComplex.support = convexHull ℝ (range (b i))) :
    (∀ (p q : (i : I) × (M i).Triangle), p ≠ q →
      CoordinateTriangleBoundaryIntersection (F p.1) (F q.1)
        (meshTriangleBasis (M p.1) p.2) (meshTriangleBasis (M q.1) q.2)) ∧
    (⋃ p : (i : I) × (M i).Triangle,
      F p.1 '' convexHull ℝ (range (meshTriangleBasis (M p.1) p.2))) =
        ⋃ i, F i '' convexHull ℝ (range (b i)) := by
  have hchild (i : I) (t : (M i).Triangle) :
      convexHull ℝ (range (meshTriangleBasis (M i) t)) ⊆ convexHull ℝ (range (b i)) := by
    rw [← hsupport]
    exact meshTriangleBasis_subset_support (M i) t
  constructor
  · rintro ⟨i, t⟩ ⟨j, u⟩ hne
    by_cases hij : i = j
    · subst j
      apply mesh_coordinate_triangle_intersection (M i) (F i)
      · rw [hsupport]
        exact hsource i
      · exact fun h => hne (Sigma.ext rfl (heq_of_eq h))
    · exact m64Intrinsic_canonical_contact_children (F i) (F j) (b i) (b j)
        (meshTriangleBasis (M i) t) (meshTriangleBasis (M j) u)
        (hsource i) (hsource j) (hchild i t) (hchild j u) (hparents i j hij)
  · ext x
    constructor
    · rintro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨p.1, image_mono (hchild p.1 p.2) hp⟩
    · rintro hx
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
      rw [← hsupport i] at hz
      rw [TriangleMesh.toPlaneComplex_support] at hz
      obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
      apply mem_iUnion.mpr
      refine ⟨⟨i, ⟨t, ht⟩⟩, z, ?_, hzx⟩
      simpa only [range_meshTriangleBasis] using hzt

end PoincareMT
