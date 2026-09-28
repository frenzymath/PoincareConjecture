import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreRefinement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Faces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.RefinementData
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.FamilyWidths










set_option autoImplicit false

open Set Classical
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]



structure RetainedCoordinateTriangulation where
  decomposition : FiniteChartRegionDecomposition (M := M)
  chart : decomposition.regions → decomposition.centers
  patches : ∀ p : decomposition.vertices,
    ChartCircleArrangementVertexPatch decomposition.radius (p : M)
  region : decomposition.vertices → Bool × Bool → decomposition.regions
  caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (patches p)
    (fun s => (chart (region p s) : M))
  cut : decomposition.EdgeIndex → Bool → ℝ
  graphs : ∀ p : decomposition.IncidentEdgeIndex,
    decomposition.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt Plane (chart p.1.1 : M)).symm (cut p.1.2 false) (1 - cut p.1.2 true)
  leftCap : ∀ p : decomposition.IncidentEdgeIndex,
    decomposition.CapGraphEndpoint patches region (fun R => (chart R : M)) caps
      p.1.2 p.1.1 ((graphs p).piece (graphs p).firstPiece) false (cut p.1.2 false)
  rightCap : ∀ p : decomposition.IncidentEdgeIndex,
    decomposition.CapGraphEndpoint patches region (fun R => (chart R : M)) caps
      p.1.2 p.1.1 ((graphs p).piece (graphs p).lastPiece) true (cut p.1.2 true)
  chains : ∀ p, (graphs p).CutChain (leftCap p).direction (rightCap p).direction
  width : ℝ
  length : ℝ
  width_pos : 0 < width
  length_pos : 0 < length
  bands : ∀ p i, ((graphs p).piece i).FixedStripBandFaces
    ((chains p).graphCuts i) width length length
  coreMeshes : decomposition.regions → TriangleMesh
  core_ancestry : ∀ R, ∃ (b : AffineBasis (Fin 3) ℝ Plane)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop),
    coreMeshes R = ((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P ∧
      (coreMeshes R).toPlaneComplex.support ⊆ interior (convexHull ℝ (range b))
  refined : decomposition.FittedCoreRefinementWithAncestry chart cut graphs chains bands caps region coreMeshes
  refinement : CompatibleCoordinateTriangleRefinement
    (decomposition.fittedFaceCoordinates chart cut graphs chains bands refined.mesh caps)
    (decomposition.fittedFaceBasis chart cut graphs chains bands refined.mesh caps)
  chart_source : ∀ R : decomposition.regions, closure (connectedComponentIn
    (chartDiskBoundaryUnion decomposition.centers decomposition.radius)ᶜ R) ⊆
      (chartAt Plane (chart R : M)).source
  patches_disjoint : ∀ p q, p ≠ q → Disjoint (patches p).carrier (patches q).carrier
  cap_regions : ∀ p s, ((caps p).face s).carrier ⊆ closure (connectedComponentIn
    (chartDiskBoundaryUnion decomposition.centers decomposition.radius)ᶜ (region p s))
  cut_mem : ∀ e t, cut e t ∈ Ioo (0 : ℝ) (1 / 3)
  length_le_one : length ≤ 1
  length_lt_one : length < 1
  strip_adjacent : ∀ p (i j : Fin (graphs p).count), i.succ = j.castSucc →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < width → |w| < width →
        ((graphs p).piece i).strip ((chains p).graphCuts i) (t, z) =
          ((graphs p).piece j).strip ((chains p).graphCuts j) (s, w) → t = 1 ∧ s = 0
  strip_separate : ∀ i j : decomposition.IncidentGraphPieceIndex chart cut graphs,
    decomposition.IncidentGraphPiecesSeparated chart cut graphs i j → Disjoint
      (((graphs i.1).piece i.2).strip ((chains i.1).graphCuts i.2) ''
        (Icc (0 : ℝ) 1 ×ˢ Ioo (-width) width))
      (((graphs j.1).piece j.2).strip ((chains j.1).graphCuts j.2) ''
        (Icc (0 : ℝ) 1 ×ˢ Ioo (-width) width))
  band_regions : ∀ p i, (bands p i).faces.carrier ⊆ closure (connectedComponentIn
    (chartDiskBoundaryUnion decomposition.centers decomposition.radius)ᶜ p.1.1)
  band_boundary : ∀ p i, (bands p i).faces.carrier ∩
    chartDiskBoundaryUnion decomposition.centers decomposition.radius =
      (decomposition.edge p.1.2.1 p.1.2.2).map ''
        Icc ((graphs p).cut i.castSucc) ((graphs p).cut i.succ)
  band_adjacent : ∀ p (i j : Fin (graphs p).count), i.succ = j.castSucc →
    (bands p i).faces.carrier ∩ (bands p j).faces.carrier =
      (chartAt Plane (chart p.1.1 : M)).symm '' segment ℝ
        (chartAt Plane (chart p.1.1 : M)
          ((decomposition.edge p.1.2.1 p.1.2.2).map ((graphs p).cut i.succ)))
        (chartAt Plane (chart p.1.1 : M)
          ((decomposition.edge p.1.2.1 p.1.2.2).map ((graphs p).cut i.succ)) +
            length • (chains p).direction i.succ)
  band_caps : ∀ p i, (bands p i).faces.carrier ∩
    decomposition.vertexCapsInRegion caps region p.1.1 =
      (if i = (graphs p).firstPiece then (leftCap p).chordSegment length else ∅) ∪
        (if i = (graphs p).lastPiece then (rightCap p).chordSegment length else ∅)
  core_planar : ∀ R, (coreMeshes R).toPlaneComplex.support =
    closure ((chartAt Plane (chart R : M)) ''
      (connectedComponentIn (chartDiskBoundaryUnion decomposition.centers decomposition.radius)ᶜ R \
        decomposition.fittedRegionCollar chart cut graphs chains bands caps region R))
  core_back : ∀ R, (chartAt Plane (chart R : M)).symm '' (coreMeshes R).toPlaneComplex.support =
    closure (connectedComponentIn (chartDiskBoundaryUnion decomposition.centers decomposition.radius)ᶜ R \
      decomposition.fittedRegionCollar chart cut graphs chains bands caps region R)
  core_frontier : ∀ R, ((chartAt Plane (chart R : M)).symm '' (coreMeshes R).toPlaneComplex.support) ∩
    decomposition.fittedRegionCollar chart cut graphs chains bands caps region R ⊆
      frontier (decomposition.fittedRegionCollar chart cut graphs chains bands caps region R)

namespace RetainedCoordinateTriangulation

variable (T : RetainedCoordinateTriangulation (M := M))

omit [T2Space M] in
theorem caps_disjoint_of_vertices_ne (p q : T.decomposition.vertices) (hpq : p ≠ q)
    (i j : Bool × Bool) : Disjoint ((T.caps p).face i).carrier ((T.caps q).face j).carrier :=
  (T.patches_disjoint p q hpq).mono ((T.caps p).carrier_subset_patch i)
    ((T.caps q).carrier_subset_patch j)

omit [T2Space M] in
theorem bands_disjoint_of_separated
    (i j : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs)
    (hij : T.decomposition.IncidentGraphPiecesSeparated T.chart T.cut T.graphs i j) :
    Disjoint (T.bands i.1 i.2).faces.carrier (T.bands j.1 j.2).faces.carrier :=
  (T.strip_separate i j hij).mono (T.bands i.1 i.2).carrier_subset_open_strip
    (T.bands j.1 j.2).carrier_subset_open_strip

omit [T2Space M] in
theorem refined_core_back (R : T.decomposition.regions) :
    (chartAt Plane (T.chart R : M)).symm '' (T.refined.mesh R).toPlaneComplex.support =
      closure (connectedComponentIn
        (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R \
          T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands T.caps T.region R) := by
  rw [T.refined.support R]
  exact T.core_back R

omit [T2Space M] in
theorem refined_core_frontier (R : T.decomposition.regions) :
    ((chartAt Plane (T.chart R : M)).symm '' (T.refined.mesh R).toPlaneComplex.support) ∩
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands T.caps T.region R ⊆
        frontier (T.decomposition.fittedRegionCollar
          T.chart T.cut T.graphs T.chains T.bands T.caps T.region R) := by
  rw [T.refined.support R]
  exact T.core_frontier R

abbrev Parent := T.decomposition.FittedFaceIndex T.chart T.cut T.graphs T.chains T.bands T.refined.mesh

noncomputable abbrev parentCoordinates :=
  T.decomposition.fittedFaceCoordinates T.chart T.cut T.graphs T.chains T.bands T.refined.mesh T.caps

noncomputable abbrev parentBasis :=
  T.decomposition.fittedFaceBasis T.chart T.cut T.graphs T.chains T.bands T.refined.mesh T.caps

omit [T2Space M] in
theorem parent_smooth (i : T.Parent) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (T.parentCoordinates i) (T.parentCoordinates i).source :=
  T.decomposition.fittedFaceCoordinates_smooth T.chart T.cut T.graphs T.chains T.bands
    T.refined.mesh T.caps i

omit [T2Space M] in
theorem parent_symm_smooth (i : T.Parent) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (T.parentCoordinates i).symm (T.parentCoordinates i).target :=
  T.decomposition.fittedFaceCoordinates_symm_smooth T.chart T.cut T.graphs T.chains T.bands
    T.refined.mesh T.caps i

omit [T2Space M] in
theorem parent_source (i : T.Parent) :
    convexHull ℝ (range (T.parentBasis i)) ⊆ (T.parentCoordinates i).source :=
  T.decomposition.fittedFaceBasis_subset_source T.chart T.cut T.graphs T.chains T.bands
    T.refined.mesh T.caps T.refined.source i

end RetainedCoordinateTriangulation

end PoincareConjecture.Topology.Surface
