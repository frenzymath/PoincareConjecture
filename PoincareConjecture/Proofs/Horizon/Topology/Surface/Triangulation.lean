import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartTriangles
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartCircle
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartLevel
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.BoundaryRefinement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Refinement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.LevelSets
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Separation
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.LocalFiniteness
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Incidence
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.ClosureCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Decomposition
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Caps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Data
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapEndpoints
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapWidths
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.FamilyWidths
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Interfaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.RegionBands
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapAttachments
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Neighborhoods
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Neighborhoods
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Faces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CapIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CrossRegionCapBands
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.BandFamilyIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreRefinement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Retained
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Closure

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

theorem exists_finite_chart_cover (hM : IsCompact (Set.univ : Set M)) :
    ∃ (s : Finset M), (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) =
      (univ : Set M) := by
  classical
  have hopen : ∀ x : M, IsOpen ((chartAt (EuclideanSpace ℝ (Fin 2)) x).source) :=
    fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source
  have hsub : ∀ x : M, x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source :=
    fun x => mem_chart_source _ _
  obtain ⟨s, hsu⟩ := hM.elim_finite_subcover
    (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) hopen
    (by intro x hx; exact mem_iUnion.mpr ⟨x, hsub x⟩)
  refine ⟨s, ?_⟩
  apply Subset.antisymm
  · intro x hx
    exact mem_univ x
  · intro x hx
    exact hsu hx

theorem exists_finite_chart_cover_of_compact_space [CompactSpace M] :
    ∃ (s : Finset M), (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) =
      (univ : Set M) :=
  exists_finite_chart_cover (isCompact_univ : IsCompact (univ : Set M))

theorem exists_finite_smooth_triangulation_with_retained_coordinates
    [CompactSpace M] :
    Nonempty (RetainedCoordinateTriangulation (M := M)) := by
  classical
  obtain ⟨decomposition⟩ := exists_finite_chart_region_decomposition (M := M)
  obtain ⟨chart, patches, region, caps, cut, hchart, hcenters, hdisjoint, havoid,
    hlocal, hsectors, hclosedSectors, hcapRegions, hcapDisjoint, hmatch,
    hcapMiddle, hcapOpenMiddle, hneighborhood⟩ :=
    decomposition.exists_region_vertex_caps
  obtain ⟨graphs⟩ := decomposition.exists_incident_middleArc_graph_family
    chart hchart cut (fun e t => (hmatch e t).1)
  have capChains := fun p : decomposition.IncidentEdgeIndex =>
    decomposition.exists_cap_attached_cutChain patches region (fun R => (chart R : M))
      caps hdisjoint hsectors hclosedSectors p.1.2 p.1.1 p.2
      (cut p.1.2) (hmatch p.1.2) (graphs p)
  choose leftCap rightCap hchains using capChains
  let chains := fun p => Classical.choice (hchains p)
  have hcut := fun e t => (hmatch e t).1
  have hradial (e : decomposition.EdgeIndex) (t : Bool) : ∃ d : Bool × Bool,
      (patches (decomposition.edgeEndpoint e t)).radialSide d
          (caps (decomposition.edgeEndpoint e t)).scale =
        decomposition.edgeFromEndpoint e t '' Icc 0 (cut e t) := by
    obtain ⟨i, j, k, _, hk, hi, _⟩ := (hmatch e t).2
    exact (caps (decomposition.edgeEndpoint e t)).exists_radialSide_eq_of_boundary_match i k hk hi
  choose capWidth hcapWidthPos hcapWidthRadius hcapWidthSource hcapWidthAvoid using
    fun p i => (chains p).exists_cap_avoiding_width patches region (fun R => (chart R : M))
      caps hdisjoint hlocal cut hcut hradial (leftCap p) (rightCap p) i
  obtain ⟨width, hwidth, hstripRegions, hstripAdjacent, hstripSeparate⟩ :=
    decomposition.exists_incident_graph_strip_width chart cut graphs hcut
      (fun p => (leftCap p).direction) (fun p => (rightCap p).direction)
      chains capWidth hcapWidthPos
  choose lengthBound hlengthBoundPos hband using
    fun (p : decomposition.IncidentEdgeIndex) (i : Fin (graphs p).count) =>
      ((graphs p).piece i).exists_fixedStripBandFaces ((chains p).graphCuts i)
        (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
        (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) ((graphs p).cut_lt i)
        hwidth (hstripRegions p i).2.1 (chart p.1.1 : M) Subset.rfl
  choose internalLength hinternalLengthPos hinternalFree using fun p =>
    (chains p).exists_all_internal_cap_free_length patches region (fun R => (chart R : M))
      caps hdisjoint hlocal cut hcut hradial
  let bound := fun j : decomposition.IncidentGraphPieceIndex chart cut graphs =>
    min (lengthBound j.1 j.2)
      (min (leftCap j.1).length (min (rightCap j.1).length (internalLength j.1)))
  have hbound : ∀ j, 0 < bound j := fun j =>
    lt_min (hlengthBoundPos j.1 j.2)
      (lt_min (leftCap j.1).length_mem.1
        (lt_min (rightCap j.1).length_mem.1 (hinternalLengthPos j.1)))
  obtain ⟨r, hr, hbounds⟩ := Poincare.Topology.Plane.Curves.exists_pos_le_finite_family bound hbound
  let length := min (r / 2) (1 / 4)
  have hlength : 0 < length := lt_min (half_pos hr) (by norm_num)
  have hlengthr : length < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hlengthBound (p : decomposition.IncidentEdgeIndex) (i : Fin (graphs p).count) :
      length ∈ Ioo (0 : ℝ) (lengthBound p i) :=
    ⟨hlength, hlengthr.trans_le ((hbounds ⟨p, i⟩).trans (min_le_left _ _))⟩
  let bands := fun (p : decomposition.IncidentEdgeIndex) (i : Fin (graphs p).count) =>
    Classical.choice (hband p i length (hlengthBound p i) length (hlengthBound p i))
  have hlengthOne : length ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hlengthLtOne : length < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hlengthInternal (p : decomposition.IncidentEdgeIndex) : length ≤ internalLength p :=
    hlengthr.le.trans ((hbounds ⟨p, (graphs p).firstPiece⟩).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hbandCaps := fun p i => (chains p).band_inter_region_caps
    (leftCap p) (rightCap p) hlengthOne
    (fun j hj0 hjlast u hu => hinternalFree p j hj0 hjlast u
      ⟨hu.1, hu.2.trans (hlengthInternal p)⟩) i (bands p i)
    (fun t ht z hz => hcapWidthAvoid p i t ht z (hz.trans_le (hstripRegions p i).1))
  have hbandAdjacent := fun p i j hij => (chains p).adjacent_band_intersection
    (bands p) i j hij (hstripAdjacent p i j hij)
  have hbandRegions := fun p i => (bands p i).carrier_subset_region_closure
    (fun t ht z hz hzw => ((hstripRegions p i).2.2 t ht z
      (by rwa [abs_of_nonneg hz])).2.2.2 hz)
  have hbandBoundary := fun p i => (bands p i).carrier_inter_arrangement ((graphs p).cut_lt i)
    (fun t ht z hz hzw => ((hstripRegions p i).2.2 t ht z
      (by rwa [abs_of_nonneg hz])).2.1)
  obtain ⟨vertexNeighborhood, hvertexOpen, hvertices, hvertexCover⟩ := hneighborhood
  have hregionalVertices := fun R => decomposition.region_vertex_caps_cover_closure
    caps region hcapRegions hvertexOpen hvertexCover R
  have hminimalMatch (a : decomposition.EdgeIndex) (b : Bool) :
      ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
        (((caps (decomposition.edgeEndpoint a b)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
          decomposition.edgeFromEndpoint a b '' Icc 0 (cut a b) ∧
        ∀ s, s = i ∨ s = j → (((caps (decomposition.edgeEndpoint a b)).face s).boundary k).map 1 =
          decomposition.edgeFromEndpoint a b (cut a b) := by
    obtain ⟨i, j, k, hij, hk, hi, _, hend⟩ := (hmatch a b).2
    exact ⟨i, j, k, hij, hk, hi, fun s hs => (hend s hs).2.1⟩
  have hcollarFrontier := fun R => decomposition.frontier_fittedRegionCollar_subset
    chart cut graphs region caps leftCap rightCap chains bands hstripAdjacent hcapRegions
    (fun p i t ht z hz => hcapWidthAvoid p i t ht z (hz.trans_le (hstripRegions p i).1))
    hdisjoint hlocal hsectors hclosedSectors
    (fun a b => ⟨(hcut a b).1, (hcut a b).2.trans (by norm_num)⟩)
    hminimalMatch hlengthOne R
  have hpositive := fun p i t ht z (hz : 0 < z) (hzw : z < width) =>
    (((hstripRegions p i).2.2 t ht z (by rwa [abs_of_pos hz])).2.2.1).2 hz
  have hinterfaceAvoid := fun R => decomposition.fittedRegionInterface_disjoint_arrangement
    chart cut graphs chains bands caps region hlocal hcapRegions hpositive hlength R
  have hcollarCover := fun R q => decomposition.exists_fittedRegionCollar_neighborhood
    chart cut graphs chains bands region caps leftCap rightCap hbandRegions hcapRegions
    hvertexOpen hvertices hvertexCover R
    (decomposition.isCompact_fittedRegionInterface chart cut graphs chains bands caps region
      hlength.le R).isClosed (hinterfaceAvoid R) (hcollarFrontier R) (q := q)
  choose interfaceLines hlineSurjective hlineCover using fun R =>
    decomposition.exists_fittedRegionInterface_chart_lines chart cut graphs chains bands
      caps region (fun _ _ => rfl) hlength.le R
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  have hregionCompact (R : decomposition.regions) : IsCompact (closure (connectedComponentIn
      (chartDiskBoundaryUnion decomposition.centers decomposition.radius)ᶜ R)) := by
    obtain ⟨_, _, _, _, hcompact, _⟩ :=
      decomposition.region_containment R (decomposition.regions_outside R R.property)
    exact hcompact
  have hcores := fun R => exists_exact_polygonal_remainder_mesh_with_refinement (chart R : M)
    (isClosed_chartDiskBoundaryUnion decomposition.centers decomposition.radius).isOpen_compl.connectedComponentIn
    (hregionCompact R) (hchart R)
    (fun _ : Unit => decomposition.fittedRegionCollar chart cut graphs chains bands caps region R)
    (fun _ => (decomposition.isCompact_fittedRegionCollar chart cut graphs chains bands caps region R).isClosed)
    (fun _ => decomposition.fittedRegionCollar_subset_region_closure
      chart cut graphs chains bands caps region hbandRegions hcapRegions R)
    (decomposition.region_frontier_subset_arrangement R) (interfaceLines R) (hlineSurjective R)
    (fun _ _ hq => (hcollarFrontier R hq).elim Or.inl
      (fun h => Or.inr (hlineCover R (mem_image_of_mem _ h))))
    (fun q hq => by simpa only [iUnion_const] using hcollarCover R q hq)
  simp only [iUnion_const] at hcores
  choose coreMeshes hcorePlanar hcoreTarget hcoreBack hcoreRegion hcoreCover hcoreInter
    coreEnclosing coreLines corePredicate hcoreAncestry using hcores
  have hcutOne (e : decomposition.EdgeIndex) (t : Bool) : cut e t ∈ Ioo (0 : ℝ) 1 :=
    ⟨(hcut e t).1, (hcut e t).2.trans (by norm_num)⟩
  have hmatchedTips (e : decomposition.EdgeIndex) (t : Bool) :
      ∃ i j : Bool × Bool, ∃ k : Fin 3, i ≠ j ∧ (k = 1 ∨ k = 2) ∧
        ∀ s, s = i ∨ s = j → (((caps (decomposition.edgeEndpoint e t)).face s).boundary k).map 1 =
          decomposition.edgeFromEndpoint e t (cut e t) := by
    obtain ⟨i, j, k, hij, hk, _, hend⟩ := hminimalMatch e t
    exact ⟨i, j, k, hij, hk, hend⟩
  have hcapBands (v : decomposition.vertices) (s : Bool × Bool)
      (p : decomposition.IncidentEdgeIndex) (i : Fin (graphs p).count)
      (j : Fin (bands p i).faces.interface.count × Bool) :
      CoordinateTriangleBoundaryIntersection ((caps v).coordinates s)
        ((bands p i).faces.faceCoordinates j)
        (Poincare.Topology.Plane.Triangles.rightTriangleBasis (caps v).scale_pos)
        ((bands p i).faces.faceBasis j) := by
    by_cases hs : region v s = p.1.1
    · exact (chains p).cap_band_face_coordinate_intersection (leftCap p) (rightCap p) i
        (bands p i) ((min_le_right _ _).trans_lt (by norm_num))
        hdisjoint hsectors hclosedSectors (hcutOne p.1.2) (hmatchedTips p.1.2)
        (hbandCaps p i) v s hs j
    · exact decomposition.cross_region_cap_band_coordinate_intersection patches caps
        hdisjoint hlocal cut hcut hradial region hclosedSectors ((graphs p).piece i)
        (bands p i) ((graphs p).cut_lt i) ((graphs p).piece_interval_subset i)
        (fun t ht z hz hzw => ((hstripRegions p i).2.2 t ht z
          (by rwa [abs_of_nonneg hz])).2.1) (hbandRegions p i) v s hs j
  obtain ⟨refined⟩ := decomposition.exists_fittedCoreRefinement_with_ancestry chart cut graphs chains bands
    caps region (fun _ _ => rfl) hcapRegions coreMeshes hcoreTarget hcoreRegion hcoreCover
    (fun R q hq => (hcoreInter R () hq).1)
  have hcoreCaps (R : decomposition.regions) (t : (refined.mesh R).Triangle)
      (v : decomposition.vertices) (s : Bool × Bool) :
      CoordinateTriangleBoundaryIntersection
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R : M)).symm ((caps v).coordinates s)
        (meshTriangleBasis (refined.mesh R) t)
        (Poincare.Topology.Plane.Triangles.rightTriangleBasis (caps v).scale_pos) := by
    by_cases hR : R = region v s
    · subst R
      exact refined.cap_contact v s t
    · exact decomposition.cross_region_core_cap_coordinate_intersection hR (refined.mesh R)
        _ (caps v) s (refined.in_region R) (hcapRegions v s) t
  have hcoreBands (R : decomposition.regions) (t : (refined.mesh R).Triangle)
      (p : decomposition.IncidentEdgeIndex) (i : Fin (graphs p).count)
      (j : Fin (bands p i).faces.interface.count × Bool) :
      CoordinateTriangleBoundaryIntersection
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R : M)).symm
        ((bands p i).faces.faceCoordinates j) (meshTriangleBasis (refined.mesh R) t)
        ((bands p i).faces.faceBasis j) := by
    by_cases hR : R = p.1.1
    · subst R
      exact refined.band_contact p i t j
    · exact decomposition.cross_region_core_band_coordinate_intersection hR (refined.mesh R)
        _ _ (bands p i).faces (refined.in_region R) (hbandRegions p i) t j
  have hcoreCore (a b : Σ R : decomposition.regions, (refined.mesh R).Triangle) (hab : a ≠ b) :
      CoordinateTriangleBoundaryIntersection
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart a.1 : M)).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart b.1 : M)).symm
        (meshTriangleBasis (refined.mesh a.1) a.2) (meshTriangleBasis (refined.mesh b.1) b.2) := by
    rcases a with ⟨R, t⟩
    rcases b with ⟨S, v⟩
    by_cases hR : R = S
    · subst S
      exact mesh_coordinate_triangle_intersection (refined.mesh R) _ (refined.source R) t v
        (fun h => hab (h ▸ rfl))
    · exact decomposition.cross_region_core_coordinate_intersection hR
        (refined.mesh R) (refined.mesh S) _ _ (refined.in_region R) (refined.in_region S) t v
  have hparents : ∀ a b, a ≠ b →
      CoordinateTriangleBoundaryIntersection
        (decomposition.fittedFaceCoordinates chart cut graphs chains bands refined.mesh caps a)
        (decomposition.fittedFaceCoordinates chart cut graphs chains bands refined.mesh caps b)
        (decomposition.fittedFaceBasis chart cut graphs chains bands refined.mesh caps a)
        (decomposition.fittedFaceBasis chart cut graphs chains bands refined.mesh caps b) := by
    intro a b hab
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    · exact decomposition.vertex_caps_coordinate_intersection caps hdisjoint
        (fun h => hab (h ▸ rfl))
    · exact hcapBands a.1 a.2 b.1.1 b.1.2 b.2
    · exact (hcoreCaps b.1 b.2 a.1 a.2).symm
    · exact (hcapBands b.1 b.2 a.1.1 a.1.2 a.2).symm
    · exact decomposition.band_family_faces_coordinate_intersection chart cut graphs chains bands
        hcut hstripAdjacent hstripSeparate hbandRegions
        (fun p i t ht z hz hzw => ((hstripRegions p i).2.2 t ht z
          (by rwa [abs_of_nonneg hz])).2.1) a b (fun h => hab (h ▸ rfl))
    · exact (hcoreBands b.1 b.2 a.1.1 a.1.2 a.2).symm
    · exact hcoreCaps a.1 a.2 b.1 b.2
    · exact hcoreBands a.1 a.2 b.1.1 b.1.2 b.2
    · exact hcoreCore a b (fun h => hab (h ▸ rfl))
  let parentCoordinates := decomposition.fittedFaceCoordinates chart cut graphs chains bands refined.mesh caps
  let parentBasis := decomposition.fittedFaceBasis chart cut graphs chains bands refined.mesh caps
  obtain ⟨refinement⟩ := nonempty_compatibleCoordinateTriangleRefinement
    parentCoordinates parentBasis
    (fun a => decomposition.fittedFaceCoordinates_smooth chart cut graphs chains bands refined.mesh caps a)
    (fun a => decomposition.fittedFaceCoordinates_symm_smooth chart cut graphs chains bands refined.mesh caps a)
    (fun a => decomposition.fittedFaceBasis_subset_source chart cut graphs chains bands refined.mesh caps refined.source a)
    (decomposition.fittedFaceChart chart cut graphs chains bands refined.mesh)
    (fun a => decomposition.fittedFaceCoordinates_subset_chart chart cut graphs chains bands refined.mesh caps refined.source a)
    hparents (decomposition.fittedFaceCoordinates_cover chart cut graphs chains bands refined.mesh caps region refined.cover)
  refine ⟨{
    decomposition := decomposition
    chart := chart
    patches := patches
    region := region
    caps := caps
    cut := cut
    graphs := graphs
    leftCap := leftCap
    rightCap := rightCap
    chains := chains
    width := width
    length := length
    width_pos := hwidth
    length_pos := hlength
    bands := bands
    coreMeshes := coreMeshes
    core_ancestry := fun R => ⟨coreEnclosing R, coreLines R, corePredicate R,
      hcoreAncestry R⟩
    refined := refined
    refinement := refinement
    chart_source := hchart
    patches_disjoint := hdisjoint
    cap_regions := hcapRegions
    cut_mem := hcut
    length_le_one := hlengthOne
    length_lt_one := hlengthLtOne
    strip_adjacent := hstripAdjacent
    strip_separate := hstripSeparate
    band_regions := hbandRegions
    band_boundary := hbandBoundary
    band_adjacent := hbandAdjacent
    band_caps := hbandCaps
    core_planar := hcorePlanar
    core_back := hcoreBack
    core_frontier := fun R q hq => (hcoreInter R () hq).1 }⟩

theorem exists_finite_smooth_triangulation_with_coordinates
    [CompactSpace M] :
    Nonempty (FiniteSmoothTriangulationWithCoordinates (M := M)) := by
  obtain ⟨T⟩ := exists_finite_smooth_triangulation_with_retained_coordinates (M := M)
  exact T.refinement.nonempty_triangulationWithCoordinates T.parent_smooth T.parent_symm_smooth

theorem exists_finite_smooth_triangulation
    [CompactSpace M] : Nonempty (FiniteSmoothTriangulation (M := M)) := by
  obtain ⟨W⟩ := exists_finite_smooth_triangulation_with_coordinates (M := M)
  exact ⟨W.triangulation⟩

end PoincareConjecture.Topology.Surface
