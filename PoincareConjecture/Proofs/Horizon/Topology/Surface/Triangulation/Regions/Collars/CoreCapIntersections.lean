


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.OuterFaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.ConnectedIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Affine.Lines
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.BoundaryContact




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)


noncomputable def chartChord (i : Bool × Bool) : Set Plane :=
  affineSegment ℝ
    (chartAt Plane (x i) (P.sectorCoordinates i (B.scale, 0)))
    (chartAt Plane (x i) (P.sectorCoordinates i (0, B.scale)))

noncomputable def chordSupportingLine (i : Bool × Bool) : Plane →ᵃ[ℝ] ℝ :=
  Classical.choose (Poincare.Topology.Plane.exists_affine_line_containing_segment
    (chartAt Plane (x i) (P.sectorCoordinates i (B.scale, 0)))
    (chartAt Plane (x i) (P.sectorCoordinates i (0, B.scale))))

omit [T2Space M] in
theorem chordSupportingLine_spec (i : Bool × Bool) :
    Function.Surjective (B.chordSupportingLine i) ∧
      B.chartChord i ⊆ {z | B.chordSupportingLine i z = 0} := by
  simpa only [chartChord, chordSupportingLine, affineSegment_eq_segment] using
    Classical.choose_spec (Poincare.Topology.Plane.exists_affine_line_containing_segment
      (chartAt Plane (x i) (P.sectorCoordinates i (B.scale, 0)))
      (chartAt Plane (x i) (P.sectorCoordinates i (0, B.scale))))

private theorem core_contact_of_monochromatic (T : TriangleMesh) (i : Bool × Bool)
    (hsource : T.toPlaneComplex.support ⊆ (chartAt Plane (x i)).target)
    (hcontact : ((chartAt Plane (x i)).symm '' T.toPlaneComplex.support) ∩
      (B.face i).carrier ⊆ ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1)
    (hmono : T.IsMonochromatic (B.chordSupportingLine i)) (t : T.Triangle) :
    CoordinateTriangleBoundaryIntersection (chartAt Plane (x i)).symm (B.coordinates i)
      (meshTriangleBasis T t) (rightTriangleBasis B.scale_pos) := by
  let C := (chartAt Plane (x i)).symm
  let K := convexHull ℝ (range (meshTriangleBasis T t))
  have hK : K ⊆ C.source := (meshTriangleBasis_subset_support T t).trans hsource
  have hA : B.chartChord i ⊆ C.source := B.chord_segment_subset_chart_target i
  have hconvex : Convex ℝ (B.chartChord i) := by
    change Convex ℝ (affineSegment ℝ _ _)
    rw [affineSegment_eq_segment]
    exact convex_segment _ _
  have hchord : C '' B.chartChord i = ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1 :=
    (B.chord_image i).symm
  have hAP : C '' B.chartChord i ⊆ (B.face i).carrier :=
    hchord.subset.trans (((B.face i).boundary_image_subset_frontier 0).trans
      (B.face i).isClosed_carrier.frontier_subset)
  have hbound : (C '' K) ∩ (B.face i).carrier ⊆ C '' B.chartChord i := by
    rw [hchord]
    exact (inter_subset_inter_left _ (image_mono (meshTriangleBasis_subset_support T t))).trans
      hcontact
  have heq : (C '' K) ∩ (B.face i).carrier = C '' (K ∩ B.chartChord i) := by
    apply subset_antisymm
    · rintro y ⟨⟨z, hz, rfl⟩, hp⟩
      obtain ⟨w, hw, hwz⟩ := hbound ⟨mem_image_of_mem C hz, hp⟩
      have hwz' := C.injOn (hA hw) (hK hz) hwz
      subst w
      exact ⟨z, ⟨hz, hw⟩, rfl⟩
    · rintro y ⟨z, ⟨hz, ha⟩, rfl⟩
      exact ⟨mem_image_of_mem C hz, hAP (mem_image_of_mem C ha)⟩
  have hside : (∀ k, 0 ≤ B.chordSupportingLine i (meshTriangleBasis T t k)) ∨
      (∀ k, B.chordSupportingLine i (meshTriangleBasis T t k) ≤ 0) := by
    have hvertices (k : Fin 3) : meshTriangleBasis T t k ∈ T.triangleCarrier t.1 := by
      change _ ∈ convexHull ℝ (T.position '' (t.1 : Set T.Vertex))
      rw [← range_meshTriangleBasis]
      exact subset_convexHull ℝ _ (mem_range_self _)
    rcases hmono.triangleCarrier_halfspace T t with hpos | hneg
    · exact Or.inl (fun k => hpos _ (hvertices k))
    · exact Or.inr (fun k => hneg _ (hvertices k))
  apply CoordinateTriangleBoundaryIntersection.of_convex_chart_contact C (B.coordinates i)
    (meshTriangleBasis T t) (rightTriangleBasis B.scale_pos) hK
    (B.triangle_subset_source i) (B.chartChord i) hconvex
    (by simpa only [← B.carrier_eq i] using heq) (B.chordSupportingLine i)
    (B.chordSupportingLine_spec i).1 hside (B.chordSupportingLine_spec i).2 0
  rw [← B.carrier_eq i]
  apply hbound.trans
  rw [hchord, B.boundary_map]
  have himage (p q : Plane) : affineChartSegment p q '' Icc (0 : ℝ) 1 =
      affineSegment ℝ p q := by
    unfold affineSegment
    congr 1
    funext u
    simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
  rw [← himage, image_image]
  exact Subset.rfl

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

variable (D : FiniteChartRegionDecomposition (M := M))
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)


noncomputable def capCoreContactLines (R : D.regions) : List (Plane →ᵃ[ℝ] ℝ) := by
  classical
  exact (Finset.univ : Finset {a : D.vertices × (Bool × Bool) // region a.1 a.2 = R}).toList.map
    (fun a => (caps a.1.1).chordSupportingLine a.1.2)

omit [T2Space M] in
theorem chordSupportingLine_mem_capCoreContactLines {R : D.regions}
    {p : D.vertices} {i : Bool × Bool} (hassign : region p i = R) :
    (caps p).chordSupportingLine i ∈ D.capCoreContactLines caps region R := by
  classical
  exact List.mem_map.mpr ⟨⟨(p, i), hassign⟩, by simp, rfl⟩

omit [T2Space M] in
theorem capCoreContactLines_surjective (R : D.regions) :
    ∀ l ∈ D.capCoreContactLines caps region R, Function.Surjective l := by
  classical
  intro l hl
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
  exact ((caps a.1.1).chordSupportingLine_spec a.1.2).1




theorem core_cap_boundaryIntersection
    (chart : D.regions → D.centers)
    (hx : ∀ p i, x p i = (chart (region p i) : M))
    (hregion : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    {R : D.regions} {p : D.vertices} {i : Bool × Bool} (hassign : region p i = R)
    (T : TriangleMesh)
    (hsource : T.toPlaneComplex.support ⊆ (chartAt Plane (chart R : M)).target)
    {collar : Set M} (hcollar : D.vertexCapsInRegion caps region R ⊆ collar)
    (hinterior : Disjoint ((chartAt Plane (chart R : M)).symm '' T.toPlaneComplex.support)
      (interior collar))
    (harrangement : Disjoint ((chartAt Plane (chart R : M)).symm '' T.toPlaneComplex.support)
      (chartDiskBoundaryUnion D.centers D.radius))
    (hmono : T.IsMonochromatic ((caps p).chordSupportingLine i)) (t : T.Triangle) :
    CoordinateTriangleBoundaryIntersection (chartAt Plane (chart R : M)).symm
      ((caps p).coordinates i) (meshTriangleBasis T t) (rightTriangleBasis (caps p).scale_pos) := by
  have hxR : x p i = (chart R : M) := by rw [hx p i, hassign]
  have hcontact := D.inter_cap_subset_chord_of_disjoint_collar_interior caps region
    hregion hassign hcollar hinterior harrangement
  simpa only [hxR] using (caps p).core_contact_of_monochromatic T i
    (by simpa only [hxR] using hsource) (by simpa only [hxR] using hcontact) hmono t



theorem core_cap_boundaryIntersections
    (chart : D.regions → D.centers)
    (hx : ∀ p i, x p i = (chart (region p i) : M))
    (hregion : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (R : D.regions) (T : TriangleMesh)
    (hsource : T.toPlaneComplex.support ⊆ (chartAt Plane (chart R : M)).target)
    {collar : Set M} (hcollar : D.vertexCapsInRegion caps region R ⊆ collar)
    (hinterior : Disjoint ((chartAt Plane (chart R : M)).symm '' T.toPlaneComplex.support)
      (interior collar))
    (harrangement : Disjoint ((chartAt Plane (chart R : M)).symm '' T.toPlaneComplex.support)
      (chartDiskBoundaryUnion D.centers D.radius))
    (hmono : ∀ l ∈ D.capCoreContactLines caps region R, T.IsMonochromatic l) :
    ∀ p i, region p i = R → ∀ t : T.Triangle,
      CoordinateTriangleBoundaryIntersection (chartAt Plane (chart R : M)).symm
        ((caps p).coordinates i) (meshTriangleBasis T t) (rightTriangleBasis (caps p).scale_pos) := by
  intro p i hassign t
  exact D.core_cap_boundaryIntersection caps region chart hx hregion hassign T hsource hcollar
    hinterior harrangement
    (hmono _ (D.chordSupportingLine_mem_capCoreContactLines caps region hassign)) t

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
