


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreBandRefinement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreCapIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CutGluing








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt Plane (chart p.1.1 : M)).symm
      (cut p.1.2 false) (1 - cut p.1.2 true))
  {dLeft dRight : D.IncidentEdgeIndex → Plane}
  (K : ∀ p, (S p).CutChain (dLeft p) (dRight p)) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)


noncomputable def fittedCoreRefinementLines (R : D.regions) : List (Plane →ᵃ[ℝ] ℝ) := by
  classical
  exact D.capCoreContactLines caps region R ++
    (Finset.univ : Finset (D.IncidentGraphPieceIndex chart cut S)).toList.flatMap
      (fun a => if a.1.1.1 = R then (B a.1 a.2).coreContactLines else [])

omit [T2Space M] in
theorem band_line_mem_fittedCoreRefinementLines (p : D.IncidentEdgeIndex)
    (i : Fin (S p).count) (l : Plane →ᵃ[ℝ] ℝ) (hl : l ∈ (B p i).coreContactLines) :
    l ∈ D.fittedCoreRefinementLines chart cut S K B caps region p.1.1 := by
  classical
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨⟨p, i⟩, by simp, by simpa using hl⟩

omit [T2Space M] in
theorem cap_line_mem_fittedCoreRefinementLines (R : D.regions)
    (l : Plane →ᵃ[ℝ] ℝ) (hl : l ∈ D.capCoreContactLines caps region R) :
    l ∈ D.fittedCoreRefinementLines chart cut S K B caps region R :=
  List.mem_append_left _ hl


structure FittedCoreRefinement (cores : D.regions → TriangleMesh) where
  mesh : D.regions → TriangleMesh
  support : ∀ R, (mesh R).toPlaneComplex.support = (cores R).toPlaneComplex.support
  subdivides : ∀ R, (mesh R).toPlaneComplex.Subdivides (cores R).toPlaneComplex
  source : ∀ R, (mesh R).toPlaneComplex.support ⊆ (chartAt Plane (chart R : M)).target
  in_region : ∀ R, (chartAt Plane (chart R : M)).symm '' (mesh R).toPlaneComplex.support ⊆
    connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R
  cover : ∀ R : D.regions, closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) =
    D.fittedRegionCollar chart cut S K B caps region R ∪
      (chartAt Plane (chart R : M)).symm '' (mesh R).toPlaneComplex.support
  band_contact : ∀ (p : D.IncidentEdgeIndex) (i : Fin (S p).count)
    (t : (mesh p.1.1).Triangle) (j : Fin (B p i).faces.interface.count × Bool),
    CoordinateTriangleBoundaryIntersection (chartAt Plane (chart p.1.1 : M)).symm
      ((B p i).faces.faceCoordinates j) (meshTriangleBasis (mesh p.1.1) t)
      ((B p i).faces.faceBasis j)
  cap_contact : ∀ (p : D.vertices) (i : Bool × Bool) (t : (mesh (region p i)).Triangle),
    CoordinateTriangleBoundaryIntersection (chartAt Plane (chart (region p i) : M)).symm
      ((caps p).coordinates i) (meshTriangleBasis (mesh (region p i)) t)
      (rightTriangleBasis (caps p).scale_pos)


structure FittedCoreRefinementWithAncestry (cores : D.regions → TriangleMesh)
    extends D.FittedCoreRefinement chart cut S K B caps region cores where
  mesh_eq_refineByLines : ∀ R, mesh R = (cores R).refineByLines
    (D.fittedCoreRefinementLines chart cut S K B caps region R)



theorem exists_fittedCoreRefinement_with_ancestry
    (hx : ∀ p i, x p i = (chart (region p i) : M))
    (hcapRegions : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (cores : D.regions → TriangleMesh)
    (hsource : ∀ R, (cores R).toPlaneComplex.support ⊆ (chartAt Plane (chart R : M)).target)
    (hregion : ∀ R, (chartAt Plane (chart R : M)).symm '' (cores R).toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
    (hcover : ∀ R : D.regions, closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) =
      D.fittedRegionCollar chart cut S K B caps region R ∪
        (chartAt Plane (chart R : M)).symm '' (cores R).toPlaneComplex.support)
    (hfrontier : ∀ R, ((chartAt Plane (chart R : M)).symm '' (cores R).toPlaneComplex.support) ∩
      D.fittedRegionCollar chart cut S K B caps region R ⊆
        frontier (D.fittedRegionCollar chart cut S K B caps region R)) :
    Nonempty (D.FittedCoreRefinementWithAncestry chart cut S K B caps region cores) := by
  classical
  let mesh := fun R => (cores R).refineByLines
    (D.fittedCoreRefinementLines chart cut S K B caps region R)
  have hs (R) : (mesh R).toPlaneComplex.support = (cores R).toPlaneComplex.support :=
    (cores R).refineByLines_support _
  have hsource' (R) : (mesh R).toPlaneComplex.support ⊆ (chartAt Plane (chart R : M)).target := by
    simpa only [hs R] using hsource R
  have hregion' (R) : (chartAt Plane (chart R : M)).symm '' (mesh R).toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
    simpa only [hs R] using hregion R
  have hmono (R) (l : Plane →ᵃ[ℝ] ℝ)
      (hl : l ∈ D.fittedCoreRefinementLines chart cut S K B caps region R) :
      (mesh R).IsMonochromatic l := (cores R).refineByLines_isMonochromatic_of_mem _ hl
  have hdisjoint (R) : Disjoint
      ((chartAt Plane (chart R : M)).symm '' (mesh R).toPlaneComplex.support)
      (interior (D.fittedRegionCollar chart cut S K B caps region R)) := by
    apply disjoint_left.mpr
    intro q hq hi
    have hq' : q ∈ (chartAt Plane (chart R : M)).symm '' (cores R).toPlaneComplex.support := by
      simpa only [hs R] using hq
    exact (hfrontier R ⟨hq', interior_subset hi⟩).2 hi
  have hboundary (R) : Disjoint
      ((chartAt Plane (chart R : M)).symm '' (mesh R).toPlaneComplex.support)
      (chartDiskBoundaryUnion D.centers D.radius) := by
    apply disjoint_left.mpr
    intro q hq hK
    exact connectedComponentIn_subset _ _ (hregion' R hq) hK
  refine ⟨{
    mesh := mesh
    mesh_eq_refineByLines := fun _ => rfl
    support := hs
    subdivides := fun R => (cores R).refineByLines_subdivides _
    source := hsource'
    in_region := hregion'
    cover := fun R => by simpa only [hs R] using hcover R
    band_contact := ?_
    cap_contact := ?_
  }⟩
  · intro p i t j
    have hband : (B p i).faces.carrier ⊆
        D.fittedRegionCollar chart cut S K B caps region p.1.1 := by
      intro q hq
      exact Or.inr (mem_iUnion.mpr ⟨⟨⟨p, i⟩, rfl⟩, hq⟩)
    have hlower : (B p i).faces.lowerArc ⊆ chartDiskBoundaryUnion D.centers D.radius := by
      rw [(K p).lowerArc_eq_original (B p) i]
      rintro q ⟨s, _, rfl⟩
      exact D.edge_mem_boundary p.1.2 s
    exact (B p i).core_boundaryIntersections_of_monochromatic (mesh p.1.1) (hsource' p.1.1)
      ((hdisjoint p.1.1).mono_right (interior_mono hband))
      ((hboundary p.1.1).mono_right hlower)
      (fun l hl => hmono p.1.1 l (D.band_line_mem_fittedCoreRefinementLines
        chart cut S K B caps region p i l hl)) t j
  · intro p i t
    exact D.core_cap_boundaryIntersections caps region chart hx hcapRegions (region p i)
      (mesh (region p i)) (hsource' (region p i)) subset_union_left
      (hdisjoint (region p i)) (hboundary (region p i))
      (fun l hl => hmono (region p i) l (D.cap_line_mem_fittedCoreRefinementLines
        chart cut S K B caps region (region p i) l hl)) p i rfl t


theorem exists_fittedCoreRefinement
    (hx : ∀ p i, x p i = (chart (region p i) : M))
    (hcapRegions : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (cores : D.regions → TriangleMesh)
    (hsource : ∀ R, (cores R).toPlaneComplex.support ⊆ (chartAt Plane (chart R : M)).target)
    (hregion : ∀ R, (chartAt Plane (chart R : M)).symm '' (cores R).toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
    (hcover : ∀ R : D.regions, closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) =
      D.fittedRegionCollar chart cut S K B caps region R ∪
        (chartAt Plane (chart R : M)).symm '' (cores R).toPlaneComplex.support)
    (hfrontier : ∀ R, ((chartAt Plane (chart R : M)).symm '' (cores R).toPlaneComplex.support) ∩
      D.fittedRegionCollar chart cut S K B caps region R ⊆
        frontier (D.fittedRegionCollar chart cut S K B caps region R)) :
    Nonempty (D.FittedCoreRefinement chart cut S K B caps region cores) := by
  obtain ⟨N⟩ := D.exists_fittedCoreRefinement_with_ancestry chart cut S K B caps region
    hx hcapRegions cores hsource hregion hcover hfrontier
  exact ⟨N.toFittedCoreRefinement⟩

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
