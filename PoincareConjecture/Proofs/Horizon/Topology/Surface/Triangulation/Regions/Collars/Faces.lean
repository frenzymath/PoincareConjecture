import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Meshes
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
      (cut p.1.2 false) (1 - cut p.1.2 true))
  {dLeft dRight : D.IncidentEdgeIndex → EuclideanSpace ℝ (Fin 2)}
  (K : ∀ p, (S p).CutChain (dLeft p) (dRight p)) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)
  (cores : D.regions → TriangleMesh)

abbrev FittedFaceIndex :=
  (D.vertices × (Bool × Bool)) ⊕
    ((Σ a : D.IncidentGraphPieceIndex chart cut S,
      Fin (B a.1 a.2).faces.interface.count × Bool) ⊕
      (Σ R : D.regions, (cores R).Triangle))

variable {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))

noncomputable def fittedFaceCoordinates
    (i : D.FittedFaceIndex chart cut S K B cores) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M :=
  Sum.elim (fun a => (caps a.1).coordinates a.2)
    (Sum.elim (fun a => (B a.1.1 a.1.2).faces.faceCoordinates a.2)
      (fun a => (chartAt (EuclideanSpace ℝ (Fin 2)) (chart a.1 : M)).symm)) i

noncomputable def fittedFaceBasis
    (i : D.FittedFaceIndex chart cut S K B cores) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Sum.elim (fun a => rightTriangleBasis (caps a.1).scale_pos)
    (Sum.elim (fun a => (B a.1.1 a.1.2).faces.faceBasis a.2)
      (fun a => meshTriangleBasis (cores a.1) a.2)) i

noncomputable def fittedFaceChart
    (i : D.FittedFaceIndex chart cut S K B cores) : M :=
  Sum.elim (fun a => x a.1 a.2)
    (Sum.elim (fun a => ((B a.1.1 a.1.2).faces.face a.2).chart)
      (fun a => (chart a.1 : M))) i

omit [T2Space M] in
theorem fittedFaceCoordinates_smooth
    (i : D.FittedFaceIndex chart cut S K B cores) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (D.fittedFaceCoordinates chart cut S K B cores caps i)
      (D.fittedFaceCoordinates chart cut S K B cores caps i).source := by
  rcases i with a | (a | a)
  · exact (caps a.1).coordinates_smooth a.2
  · exact (B a.1.1 a.1.2).faces.smooth_faceCoordinates
      (linearGraphCoordinates_contMDiff _ _
        (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
        (contMDiffOn_chart (I := 𝓡 2) (n := ∞))).1 a.2
  · exact contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞)

omit [T2Space M] in
theorem fittedFaceCoordinates_symm_smooth
    (i : D.FittedFaceIndex chart cut S K B cores) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (D.fittedFaceCoordinates chart cut S K B cores caps i).symm
      (D.fittedFaceCoordinates chart cut S K B cores caps i).target := by
  rcases i with a | (a | a)
  · exact (caps a.1).coordinates_smooth_symm a.2
  · exact (B a.1.1 a.1.2).faces.smooth_faceCoordinates_symm
      (linearGraphCoordinates_contMDiff _ _
        (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
        (contMDiffOn_chart (I := 𝓡 2) (n := ∞))).2 a.2
  · exact contMDiffOn_chart (I := 𝓡 2) (n := ∞)

omit [T2Space M] in
theorem fittedFaceBasis_subset_source
    (hcores : ∀ R, (cores R).toPlaneComplex.support ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R : M)).target)
    (i : D.FittedFaceIndex chart cut S K B cores) :
    convexHull ℝ (range (D.fittedFaceBasis chart cut S K B cores caps i)) ⊆
      (D.fittedFaceCoordinates chart cut S K B cores caps i).source := by
  rcases i with a | (a | a)
  · exact (caps a.1).triangle_subset_source a.2
  · exact (B a.1.1 a.1.2).faces.face_triangle_subset_source a.2
  · exact (meshTriangleBasis_subset_support (cores a.1) a.2).trans (hcores a.1)

omit [T2Space M] in
theorem fittedFaceCoordinates_subset_chart
    (hcores : ∀ R, (cores R).toPlaneComplex.support ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R : M)).target)
    (i : D.FittedFaceIndex chart cut S K B cores) :
    D.fittedFaceCoordinates chart cut S K B cores caps i ''
        convexHull ℝ (range (D.fittedFaceBasis chart cut S K B cores caps i)) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2))
        (D.fittedFaceChart chart cut S K B cores (x := x) i)).source := by
  rcases i with a | (a | a)
  · rintro q ⟨z, hz, rfl⟩
    exact (caps a.1).coordinates_target a.2
      (((caps a.1).coordinates a.2).mapsTo ((caps a.1).triangle_subset_source a.2 hz))
  · exact (B a.1.1 a.1.2).faces.face_coordinates_subset_chart a.2
  · rintro q ⟨z, hz, rfl⟩
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (chart a.1 : M)).symm.mapsTo
      (hcores a.1 (meshTriangleBasis_subset_support (cores a.1) a.2 hz))

omit [T2Space M] in
theorem fittedFaceCoordinates_cover
    (region : D.vertices → Bool × Bool → D.regions)
    (hcover : ∀ R : D.regions, closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) =
        D.fittedRegionCollar chart cut S K B caps region R ∪
          (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R : M)).symm ''
            (cores R).toPlaneComplex.support) :
    (⋃ i : D.FittedFaceIndex chart cut S K B cores,
      D.fittedFaceCoordinates chart cut S K B cores caps i ''
        convexHull ℝ (range (D.fittedFaceBasis chart cut S K B cores caps i))) = univ := by
  apply eq_univ_of_forall
  intro q
  have hq : q ∈ ⋃ R ∈ D.regions, closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) := by
    rw [D.region_closure_cover]
    trivial
  obtain ⟨R, hR, hq⟩ := mem_iUnion₂.mp hq
  rw [hcover ⟨R, hR⟩] at hq
  rcases hq with (hq | hq) | hq
  · obtain ⟨a, ha⟩ := mem_iUnion.mp hq
    refine mem_iUnion.mpr ⟨.inl a.1, ?_⟩
    exact (caps a.1.1).carrier_eq a.1.2 ▸ ha
  · obtain ⟨a, ha⟩ := mem_iUnion.mp hq
    obtain ⟨j, hj⟩ := mem_iUnion.mp ha
    refine mem_iUnion.mpr ⟨.inr (.inl ⟨a.1, j⟩), ?_⟩
    exact (B a.1.1 a.1.2).faces.face_carrier_eq_coordinates j ▸ hj
  · rw [← meshTriangleBasis_sources_cover, image_iUnion] at hq
    obtain ⟨t, ht⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨.inr (.inr ⟨⟨R, hR⟩, t⟩), ht⟩

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
