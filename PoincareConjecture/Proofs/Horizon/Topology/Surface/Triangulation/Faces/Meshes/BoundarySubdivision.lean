import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Subdivision.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

private theorem boundarySubdivision_segment_eq_lineMap (a b : Plane) (t : ℝ) :
    affineChartSegment a b t = AffineMap.lineMap a b t := by
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem boundarySubdivision_segment_image (a b : Plane) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  exact boundarySubdivision_segment_eq_lineMap a b t

private theorem boundarySubdivision_segment_mem_triangle
    (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t ∈
      convexHull ℝ (range b) := by
  apply segment_subset_convexHull (mem_range_self (i.succAbove 0))
    (mem_range_self (i.succAbove 1))
  rw [← affineSegment_eq_segment, ← boundarySubdivision_segment_image]
  exact mem_image_of_mem _ ht

private theorem boundarySubdivision_coord_nonneg
    (b : AffineBasis (Fin 3) ℝ Plane) {p : Plane}
    (hp : p ∈ convexHull ℝ (range b)) (i : Fin 3) : 0 ≤ b.coord i p := by
  have h : ∀ j, 0 ≤ b.coord j p := by
    simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hp
  exact h i

private theorem boundarySubdivision_coord_zero_edge
    (b : AffineBasis (Fin 3) ℝ Plane) {p : Plane}
    (hp : p ∈ convexHull ℝ (range b)) (i : Fin 3) (hi : b.coord i p = 0) :
    p ∈ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) '' Icc (0 : ℝ) 1 := by
  have hface := convexHull_inter_affine_zero_of_nonneg_set (range b) (b.coord i)
    (by rintro z ⟨j, rfl⟩; rw [b.coord_apply]; split_ifs <;> norm_num)
  have hpface : p ∈ convexHull ℝ (range b ∩ {z | b.coord i z = 0}) := by
    rw [← hface]
    exact ⟨hp, hi⟩
  rw [boundarySubdivision_segment_image, affineSegment_eq_segment, ← convexHull_pair]
  apply convexHull_mono ?_ hpface
  rintro z ⟨⟨j, rfl⟩, hj⟩
  have hji : j ≠ i := by
    intro heq
    subst j
    simp at hj
  fin_cases i <;> fin_cases j <;> simp_all [Fin.succAbove, Fin.lt_def, Fin.ext_iff]

private theorem boundarySubdivision_subsegment
    (b : AffineBasis (Fin 3) ℝ Plane) (a c : Plane) (hac : a ≠ c)
    (hboundary : affineChartSegment a c '' Icc (0 : ℝ) 1 ⊆
      frontier (convexHull ℝ (range b))) :
    ∃ (i : Fin 3) (s t : ℝ), s ∈ Icc (0 : ℝ) 1 ∧ t ∈ Icc (0 : ℝ) 1 ∧ s ≠ t ∧
      ∀ u : ℝ, affineChartSegment a c u =
        affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) (s + u * (t - s)) := by
  have hclosed := ((finite_range b).isCompact_convexHull ℝ).isClosed
  have ha : a ∈ frontier (convexHull ℝ (range b)) := by
    apply hboundary
    exact ⟨0, by simp, by simp [affineChartSegment]⟩
  have hc : c ∈ frontier (convexHull ℝ (range b)) := by
    apply hboundary
    exact ⟨1, by simp, by simp [affineChartSegment]⟩
  have hm : affineChartSegment a c (1 / 2) ∈ frontier (convexHull ℝ (range b)) :=
    hboundary ⟨1 / 2, by norm_num, rfl⟩
  have hzero : ∃ i : Fin 3, b.coord i (affineChartSegment a c (1 / 2)) = 0 := by
    by_contra! hn
    apply hm.2
    rw [b.interior_convexHull]
    intro i
    exact lt_of_le_of_ne (boundarySubdivision_coord_nonneg b (hclosed.frontier_subset hm) i)
      (hn i).symm
  obtain ⟨i, hi⟩ := hzero
  rw [boundarySubdivision_segment_eq_lineMap, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring] at hi
  have hai : b.coord i a = 0 := by
    linarith [boundarySubdivision_coord_nonneg b (hclosed.frontier_subset ha) i,
      boundarySubdivision_coord_nonneg b (hclosed.frontier_subset hc) i]
  have hci : b.coord i c = 0 := by
    linarith [boundarySubdivision_coord_nonneg b (hclosed.frontier_subset ha) i,
      boundarySubdivision_coord_nonneg b (hclosed.frontier_subset hc) i]
  obtain ⟨s, hs, hsa⟩ := boundarySubdivision_coord_zero_edge b (hclosed.frontier_subset ha) i hai
  obtain ⟨t, ht, htc⟩ := boundarySubdivision_coord_zero_edge b (hclosed.frontier_subset hc) i hci
  refine ⟨i, s, t, hs, ht, ?_, ?_⟩
  · intro hst
    exact hac (hsa.symm.trans (hst ▸ htc))
  · intro u
    rw [← hsa, ← htc]
    simp only [affineChartSegment]
    module

private theorem boundarySubdivision_open_edge_avoids_vertices
    (b : AffineBasis (Fin 3) ℝ Plane) (k : Fin 3) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) v ∉ range b := by
  rintro ⟨j, hj⟩
  have hne : k.succAbove 0 ≠ k.succAbove 1 := by
    intro h
    have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective h
    norm_num at h01
  have hc := congrArg (b.coord (k.succAbove 0)) hj
  rw [boundarySubdivision_segment_eq_lineMap, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring, b.coord_apply_eq, b.coord_apply_ne hne,
    b.coord_apply] at hc
  split_ifs at hc <;> linarith [hv.1, hv.2]

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]

structure SmoothTriangleBoundarySubdivision
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (S : Finset M) where
  mesh : TriangleMesh
  face : mesh.Triangle → SmoothFace M
  support : mesh.toPlaneComplex.support = convexHull ℝ (range b)
  subdivides : mesh.toPlaneComplex.Subdivides (TriangleMesh.single b b.ind).toPlaneComplex
  source_subset : ∀ t, convexHull ℝ (range (meshTriangleBasis mesh t)) ⊆ F.source
  map_eq : ∀ t, (face t).map = F
  source_eq : ∀ t, (face t).source = convexHull ℝ (range (meshTriangleBasis mesh t))
  carrier_eq : ∀ t, (face t).carrier = F '' convexHull ℝ (range (meshTriangleBasis mesh t))
  injective : ∀ t, InjOn (face t).map (face t).source
  boundary_map : ∀ t k, ((face t).boundary k).map = F ∘
    affineChartSegment (meshTriangleBasis mesh t (k.succAbove 0))
      (meshTriangleBasis mesh t (k.succAbove 1))
  boundary_injective : ∀ t k, InjOn ((face t).boundary k).map (Icc (0 : ℝ) 1)
  cover : (⋃ t, (face t).carrier) = F '' convexHull ℝ (range b)
  intersections : ∀ s t, s ≠ t →
    (∃ k l : Fin 3,
      (face s).carrier ∩ (face t).carrier = ((face s).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((face s).boundary k).map '' Icc (0 : ℝ) 1 =
        ((face t).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : mesh.Vertex, (face s).carrier ∩ (face t).carrier ⊆ {F (mesh.position v)}
  intersection_frontier : ∀ s t, s ≠ t →
    (face s).carrier ∩ (face t).carrier ⊆ frontier (face s).carrier
  boundary_vertices : (⋃ t, F '' range (meshTriangleBasis mesh t)) ∩
    (F '' frontier (convexHull ℝ (range b))) = (S : Set M)
  mark_vertex : ∀ p ∈ S, ∀ t, p ∈ (face t).carrier →
    p ∈ F '' range (meshTriangleBasis mesh t)
  boundary_subsegment : ∀ t k,
    ((face t).boundary k).map '' Icc (0 : ℝ) 1 ⊆
      F '' frontier (convexHull ℝ (range b)) →
    ∃ (i : Fin 3) (a c : ℝ), a ∈ Icc (0 : ℝ) 1 ∧ c ∈ Icc (0 : ℝ) 1 ∧ a ≠ c ∧
      (∀ v : ℝ, ((face t).boundary k).map v =
        F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) (a + v * (c - a)))) ∧
      ((face t).boundary k).map 0 ∈ S ∧ ((face t).boundary k).map 1 ∈ S

structure SmoothTriangleBoundarySubdivisionWithRefinement
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (S : Finset M) extends SmoothTriangleBoundarySubdivision F b S where
  refinement_lines : List (Plane →ᵃ[ℝ] ℝ)
  mesh_eq_refineByLines : mesh = (TriangleMesh.single b b.ind).refineByLines refinement_lines

theorem SmoothTriangleBoundarySubdivision.open_boundary_avoids_marks
    {F : OpenPartialHomeomorph Plane M} {b : AffineBasis (Fin 3) ℝ Plane} {S : Finset M}
    (D : SmoothTriangleBoundarySubdivision F b S) (t : D.mesh.Triangle) (k : Fin 3) :
    Disjoint (((D.face t).boundary k).map '' Ioo (0 : ℝ) 1) (S : Set M) := by
  rw [disjoint_left]
  rintro q ⟨v, hv, rfl⟩ hqS
  have hqcarrier : ((D.face t).boundary k).map v ∈ (D.face t).carrier :=
    (D.face t).isClosed_carrier.frontier_subset
      ((D.face t).boundary_image_subset_frontier k ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩)
  obtain ⟨z, hz, heq⟩ := D.mark_vertex _ hqS t hqcarrier
  rw [D.boundary_map] at heq
  have hzsrc := D.source_subset t (subset_convexHull ℝ _ hz)
  have hvsrc := D.source_subset t
    (boundarySubdivision_segment_mem_triangle (meshTriangleBasis D.mesh t) k
      ⟨hv.1.le, hv.2.le⟩)
  have hzv := F.injOn hzsrc hvsrc heq
  exact boundarySubdivision_open_edge_avoids_vertices (meshTriangleBasis D.mesh t) k hv
    (hzv ▸ hz)

theorem exists_smoothTriangleBoundarySubdivision_with_refinement
    (F : OpenPartialHomeomorph Plane M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (b : AffineBasis (Fin 3) ℝ Plane) (hsub : convexHull ℝ (range b) ⊆ F.source)
    (S : Finset M) (hS : (S : Set M) ⊆ F '' frontier (convexHull ℝ (range b)))
    (hvertices : F '' range b ⊆ (S : Set M)) (p : M)
    (hchart : F '' convexHull ℝ (range b) ⊆ (chartAt Plane p).source) :
    ∃ D : SmoothTriangleBoundarySubdivisionWithRefinement F b S,
      ∀ t, (D.face t).carrier ⊆ (chartAt Plane p).source := by
  classical
  have hclosed := ((finite_range b).isCompact_convexHull ℝ).isClosed
  have hfrontsub : frontier (convexHull ℝ (range b)) ⊆ F.source :=
    hclosed.frontier_subset.trans hsub
  have hvertexsub (i : Fin 3) : b i ∈ F.source :=
    hsub (subset_convexHull ℝ _ (mem_range_self i))
  let T : Finset Plane := S.image F.symm
  have hT : (T : Set Plane) ⊆ frontier (convexHull ℝ (range b)) := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w, hw, rfl⟩ := hS hq
    rwa [F.left_inv (hfrontsub hw)]
  have hTvertices : range b ⊆ (T : Set Plane) := by
    rintro z ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨F (b i), hvertices ⟨b i, mem_range_self i, rfl⟩,
      F.left_inv (hvertexsub i)⟩
  have hFT : F '' (T : Set Plane) = (S : Set M) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨v, hv, rfl⟩ := hS hw
      change F (F.symm (F v)) ∈ S
      rwa [F.left_inv (hfrontsub hv)]
    · intro hq
      refine ⟨F.symm q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
      obtain ⟨v, hv, rfl⟩ := hS hq
      rw [F.left_inv (hfrontsub hv)]
  obtain ⟨mesh, hsupport, hmeshboundary, hmeshmark, hsubdivides, lines, hmesh⟩ :=
    exists_triangleMesh_exact_boundary_vertices_with_refinement b T hT hTvertices
  have hmeshsub : mesh.toPlaneComplex.support ⊆ F.source := by
    rwa [hsupport]
  have hmeshchart : F '' mesh.toPlaneComplex.support ⊆ (chartAt Plane p).source := by
    rwa [hsupport]
  obtain ⟨face, hmap, hsource, hcarrier, hinj, hboundary, hedgeinj, hcover, hinter, hfrontier⟩ :=
    exists_smoothFaces_of_triangleMesh mesh F hF hFinv hmeshsub p hmeshchart
  have htriangle (t : mesh.Triangle) :
      convexHull ℝ (range (meshTriangleBasis mesh t)) ⊆ F.source :=
    (meshTriangleBasis_subset_support mesh t).trans hmeshsub
  have hmark (q : M) (hq : q ∈ S) (t : mesh.Triangle) (hqt : q ∈ (face t).carrier) :
      q ∈ F '' range (meshTriangleBasis mesh t) := by
    rw [hcarrier] at hqt
    obtain ⟨z, hz, rfl⟩ := hqt
    have hzT : z ∈ T := by
      have hinv : F.symm (F z) = z := F.left_inv (htriangle t hz)
      exact Finset.mem_image.mpr ⟨F z, hq, hinv⟩
    have hzcell : z ∈ mesh.toPlaneComplex.cellCarrier t.1 := by
      change z ∈ convexHull ℝ (mesh.position '' (t.1 : Set mesh.Vertex))
      rwa [range_meshTriangleBasis] at hz
    refine ⟨z, ?_, rfl⟩
    rw [range_meshTriangleBasis]
    exact hmeshmark z hzT t.1 t.2 hzcell
  have hboundaryvertices : (⋃ t, F '' range (meshTriangleBasis mesh t)) ∩
      (F '' frontier (convexHull ℝ (range b))) = (S : Set M) := by
    apply subset_antisymm
    · rintro q ⟨hqvertex, hqfront⟩
      obtain ⟨t, z, hz, hzq⟩ := mem_iUnion.mp hqvertex
      obtain ⟨w, hw, hwq⟩ := hqfront
      have hzsrc : z ∈ F.source := htriangle t (subset_convexHull ℝ _ hz)
      have hzw : z = w := F.injOn hzsrc (hfrontsub hw) (hzq.trans hwq.symm)
      have hzfront : z ∈ frontier (convexHull ℝ (range b)) := hzw ▸ hw
      have hzrange : z ∈ range mesh.position := by
        rw [range_meshTriangleBasis] at hz
        obtain ⟨v, -, rfl⟩ := hz
        exact mem_range_self v
      have hzT : z ∈ T := by
        change z ∈ (T : Set Plane)
        rw [← hmeshboundary]
        exact ⟨hzrange, hzfront⟩
      rw [← hFT]
      exact ⟨z, hzT, hzq⟩
    · intro q hq
      have hqfront := hS hq
      have hqcover : q ∈ ⋃ t, (face t).carrier := by
        rw [hcover, hsupport]
        exact image_mono hclosed.frontier_subset hqfront
      obtain ⟨t, hqt⟩ := mem_iUnion.mp hqcover
      exact ⟨mem_iUnion.mpr ⟨t, hmark q hq t hqt⟩, hqfront⟩
  have hsubsegment (t : mesh.Triangle) (k : Fin 3)
      (houter : ((face t).boundary k).map '' Icc (0 : ℝ) 1 ⊆
        F '' frontier (convexHull ℝ (range b))) :
      ∃ (i : Fin 3) (a c : ℝ), a ∈ Icc (0 : ℝ) 1 ∧ c ∈ Icc (0 : ℝ) 1 ∧ a ≠ c ∧
        (∀ v : ℝ, ((face t).boundary k).map v =
          F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) (a + v * (c - a)))) ∧
        ((face t).boundary k).map 0 ∈ S ∧ ((face t).boundary k).map 1 ∈ S := by
    let B := meshTriangleBasis mesh t
    have hne : B (k.succAbove 0) ≠ B (k.succAbove 1) := by
      intro heq
      have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective (B.ind.injective heq)
      norm_num at h01
    have hplanar : affineChartSegment (B (k.succAbove 0)) (B (k.succAbove 1)) ''
        Icc (0 : ℝ) 1 ⊆ frontier (convexHull ℝ (range b)) := by
      rintro z ⟨v, hv, rfl⟩
      have hsrc := htriangle t (boundarySubdivision_segment_mem_triangle B k hv)
      have hsurf : F (affineChartSegment (B (k.succAbove 0)) (B (k.succAbove 1)) v) ∈
          ((face t).boundary k).map '' Icc (0 : ℝ) 1 := by
        exact ⟨v, hv, by rw [hboundary]; rfl⟩
      obtain ⟨w, hw, heq⟩ := houter hsurf
      exact F.injOn (hfrontsub hw) hsrc heq ▸ hw
    obtain ⟨i, a, c, ha, hc, hac, hparam⟩ :=
      boundarySubdivision_subsegment b (B (k.succAbove 0)) (B (k.succAbove 1)) hne hplanar
    have hvertex (j : Fin 3) (hj : F (B j) ∈ F '' frontier (convexHull ℝ (range b))) :
        F (B j) ∈ S := by
      rw [← Finset.mem_coe, ← hboundaryvertices]
      exact ⟨mem_iUnion.mpr ⟨t, mem_image_of_mem F (mem_range_self j)⟩, hj⟩
    refine ⟨i, a, c, ha, hc, hac, ?_, ?_, ?_⟩
    · intro v
      rw [hboundary]
      change F (affineChartSegment (B (k.succAbove 0)) (B (k.succAbove 1)) v) = _
      rw [hparam]
    · have hzero : ((face t).boundary k).map 0 = F (B (k.succAbove 0)) := by
        simp [hboundary, affineChartSegment, B]
      rw [hzero]
      apply hvertex
      rw [← hzero]
      exact houter ⟨0, by simp, rfl⟩
    · have hone : ((face t).boundary k).map 1 = F (B (k.succAbove 1)) := by
        simp [hboundary, affineChartSegment, B]
      rw [hone]
      apply hvertex
      rw [← hone]
      exact houter ⟨1, by simp, rfl⟩
  refine ⟨{
    mesh := mesh
    refinement_lines := lines
    mesh_eq_refineByLines := hmesh
    face := face
    support := hsupport
    subdivides := hsubdivides
    source_subset := htriangle
    map_eq := hmap
    source_eq := hsource
    carrier_eq := hcarrier
    injective := hinj
    boundary_map := hboundary
    boundary_injective := hedgeinj
    cover := by rwa [hsupport] at hcover
    intersections := hinter
    intersection_frontier := hfrontier
    boundary_vertices := hboundaryvertices
    mark_vertex := hmark
    boundary_subsegment := hsubsegment }, ?_⟩
  intro t
  rw [hcarrier]
  exact (image_mono (meshTriangleBasis_subset_support mesh t)).trans hmeshchart

theorem exists_smoothTriangleBoundarySubdivision
    (F : OpenPartialHomeomorph Plane M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (b : AffineBasis (Fin 3) ℝ Plane) (hsub : convexHull ℝ (range b) ⊆ F.source)
    (S : Finset M) (hS : (S : Set M) ⊆ F '' frontier (convexHull ℝ (range b)))
    (hvertices : F '' range b ⊆ (S : Set M)) (p : M)
    (hchart : F '' convexHull ℝ (range b) ⊆ (chartAt Plane p).source) :
    ∃ D : SmoothTriangleBoundarySubdivision F b S,
      ∀ t, (D.face t).carrier ⊆ (chartAt Plane p).source := by
  obtain ⟨D, hD⟩ := exists_smoothTriangleBoundarySubdivision_with_refinement
    F hF hFinv b hsub S hS hvertices p hchart
  exact ⟨D.toSmoothTriangleBoundarySubdivision, hD⟩

end PoincareConjecture.Topology.Surface
