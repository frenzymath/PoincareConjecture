


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CapBandIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.RegionBands








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))

variable
  (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
  {x : D.vertices → Bool × Bool → M}
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
  (hlocal : ∀ p q, q ∈ (P p).carrier →
    (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
  (cut : D.EdgeIndex → Bool → ℝ)
  (hcut : ∀ e terminal, cut e terminal ∈ Ioo (0 : ℝ) (1 / 3))
  (hmatch : ∀ e terminal, ∃ d : Bool × Bool,
    (P (D.edgeEndpoint e terminal)).radialSide d (caps (D.edgeEndpoint e terminal)).scale =
      D.edgeFromEndpoint e terminal '' Icc 0 (cut e terminal))

include hlocal in
omit [T2Space M] in

theorem cap_arrangement_trace_subset_frontier (p : D.vertices) (s : Bool × Bool) :
    ((caps p).face s).carrier ∩ chartDiskBoundaryUnion D.centers D.radius ⊆
      frontier ((caps p).face s).carrier := by
  rintro q ⟨hq, hK⟩
  rcases (caps p).carrier_subset_sector_sides s hq with hs | hs | hs
  · exact False.elim (disjoint_left.mp ((P p).sector_disjoint_circles s) hs
      ((hlocal p q ((caps p).carrier_subset_patch s hq)).mp hK))
  · apply ((caps p).face s).boundary_image_subset_frontier 2
    rwa [(caps p).first_image]
  · apply ((caps p).face s).boundary_image_subset_frontier 1
    rwa [(caps p).second_image]

include hdisjoint hlocal hcut hmatch in

theorem cap_inter_middleArc_mem_endpoint
    (p : D.vertices) (s : Bool × Bool) (e : D.EdgeIndex) {q : M}
    (hq : q ∈ ((caps p).face s).carrier ∩ D.middleArc cut e) :
    ∃ terminal : Bool, D.edgeEndpoint e terminal = p ∧
      q = D.edgeFromEndpoint e terminal (cut e terminal) := by
  obtain ⟨t, ht, rfl⟩ := hq.2
  have ht01 : t ∈ Icc (0 : ℝ) 1 := by
    have hp := D.middleArc_parameters hcut e
    exact ⟨hp.1.le.trans ht.1, ht.2.trans hp.2.2.le⟩
  obtain ⟨terminal, hp, u, hu, heq⟩ := D.vertex_caps_inter_edge_mem_endpoint_segment
    P caps hdisjoint hlocal cut hcut hmatch p e (mem_iUnion.mpr ⟨s, hq.1⟩) ⟨t, ht01, rfl⟩
  refine ⟨terminal, hp, ?_⟩
  cases terminal
  · have hu01 : u ∈ Icc (0 : ℝ) 1 :=
      ⟨hu.1, hu.2.trans ((hcut e false).2.le.trans (by norm_num))⟩
    have hut : u = t := D.edge_injective e.1 e.2 hu01 ht01 heq
    have htcut : t = cut e false := le_antisymm (hut ▸ hu.2) ht.1
    exact congrArg (D.edge e.1 e.2).map htcut
  · have hu01 : 1 - u ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hu.1, hu.2, (hcut e true).2]
    have hut : 1 - u = t := D.edge_injective e.1 e.2 hu01 ht01 heq
    have htcut : t = 1 - cut e true := by linarith [hu.2, ht.2]
    exact congrArg (D.edge e.1 e.2).map htcut

include hdisjoint hlocal hcut hmatch in

theorem cap_inter_middleArc_subsingleton (p : D.vertices) (s : Bool × Bool) (e : D.EdgeIndex) :
    (((caps p).face s).carrier ∩ D.middleArc cut e).Subsingleton := by
  intro q hq z hz
  obtain ⟨t, htp, hq⟩ := D.cap_inter_middleArc_mem_endpoint P caps hdisjoint hlocal cut hcut hmatch
    p s e hq
  obtain ⟨u, hup, hz⟩ := D.cap_inter_middleArc_mem_endpoint P caps hdisjoint hlocal cut hcut hmatch
    p s e hz
  have htu := D.edgeEndpoint_injective e (htp.trans hup.symm)
  subst u
  exact hq.trans hz.symm

variable
  (region : D.vertices → Bool × Bool → D.regions)
  (hclosed : ∀ p s, (P p).closedSector s ⊆ closure (connectedComponentIn
    (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p s)))
  {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  (G : D.OrientedGraphPiece e R C a b)
  {ua wa ub wb δ ra rb : ℝ}
  {Q : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  (B : G.FixedStripBandFaces Q δ ra rb)

include hdisjoint hlocal hcut hmatch hclosed in


theorem cross_region_cap_band_coordinate_intersection
    (hab : a < b) (hI : Icc a b ⊆ Icc (cut e false) (1 - cut e true))
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 ≤ z → z < δ →
      (G.strip Q (t, z) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0))
    (hregion : B.faces.carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R))
    (p : D.vertices) (s : Bool × Bool) (hne : region p s ≠ R)
    (j : Fin B.faces.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection ((caps p).coordinates s) (B.faces.faceCoordinates j)
      (rightTriangleBasis (caps p).scale_pos) (B.faces.faceBasis j) := by
  have hface : (B.faces.face j).carrier ⊆ B.faces.carrier :=
    subset_iUnion (fun v => (B.faces.face v).carrier) j
  have htrace := D.inter_eq_arrangement_traces hne
    (fun q hq => D.region_closure_diff_arrangement_subset (region p s)
      ⟨hclosed p s ((caps p).carrier_subset_sector s hq.1), hq.2⟩)
    (fun q hq => D.region_closure_diff_arrangement_subset R ⟨hregion (hface hq.1), hq.2⟩)
  have hK : ((caps p).face s).carrier ∩ (B.faces.face j).carrier ⊆
      chartDiskBoundaryUnion D.centers D.radius := fun _ hq => (htrace ▸ hq).1.2
  have hbase : B.faces.lowerArc = (D.edge e.1 e.2).map '' Icc a b := by
    simpa only [ObliqueBandFaces.lowerArc, linearGraphCoordinates_apply,
      collarParameterEquiv.apply_symm_apply] using G.graph_image
  have hsub : ((caps p).face s).carrier ∩ (B.faces.face j).carrier ⊆
      ((caps p).face s).carrier ∩ D.middleArc cut e := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    have hqarc : q ∈ (D.edge e.1 e.2).map '' Icc a b := by
      rw [← B.carrier_inter_arrangement hab hzero]
      exact ⟨hface hq.2, hK hq⟩
    exact image_mono hI hqarc
  have hs : (((caps p).face s).carrier ∩ (B.faces.face j).carrier).Subsingleton :=
    fun _ hq _ hz => D.cap_inter_middleArc_subsingleton P caps hdisjoint hlocal cut hcut hmatch
      p s e (hsub hq) (hsub hz)
  by_cases hn : (((caps p).face s).carrier ∩ (B.faces.face j).carrier).Nonempty
  · obtain ⟨q, hq⟩ := hn
    apply CoordinateTriangleBoundaryIntersection.point q
    · rw [← (caps p).face_frontier_eq_coordinates]
      exact D.cap_arrangement_trace_subset_frontier P caps hlocal p s ⟨hq.1, hK hq⟩
    · rw [← B.faces.face_frontier_eq_coordinates]
      have hqbase : q ∈ B.faces.lowerArc := by
        rw [hbase, ← B.carrier_inter_arrangement hab hzero]
        exact ⟨hface hq.2, hK hq⟩
      have hfront := B.faces.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inl hqbase)))
      exact ⟨subset_closure hq.2, fun h => hfront.2 (interior_mono hface h)⟩
    · rw [← (caps p).carrier_eq, ← B.faces.face_carrier_eq_coordinates]
      exact fun _ hz => hs hz hq
  · apply CoordinateTriangleBoundaryIntersection.disjoint
    rw [← (caps p).carrier_eq, ← B.faces.face_carrier_eq_coordinates]
    exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
