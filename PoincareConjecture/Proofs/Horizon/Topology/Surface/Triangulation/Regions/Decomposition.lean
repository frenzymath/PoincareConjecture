import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.BoundaryRefinement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.ClosureCover

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

structure FiniteChartRegionDecomposition where
  centers : Finset M
  radius : M → ℝ
  radius_pos : ∀ p ∈ centers, 0 < radius p
  closedBall_subset_target : ∀ p ∈ centers,
    closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (radius p) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).target
  disk_cover : (⋃ p ∈ centers, (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
    ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (radius p)) = (univ : Set M)
  circle_intersections_finite : ∀ p ∈ centers, ∀ q ∈ centers, p ≠ q →
    (chartCircle p (radius p) ∩ chartCircle q (radius q)).Finite
  no_triple : ∀ p ∈ centers, ∀ q ∈ centers, ∀ z ∈ centers, p ≠ q → p ≠ z → q ≠ z →
    ∀ x ∈ chartCircle p (radius p), x ∈ chartCircle q (radius q) →
      x ∉ chartCircle z (radius z)
  circle_regular : ∀ p ∈ centers, ∀ q ∈ centers, p ≠ q →
    ChartCircleRegularAlong p (radius p) q (radius q) ∨
      ChartCircleRegularAlong q (radius q) p (radius p)
  edgeCount : (centers × Fin 2) → ℕ
  cut : ∀ i, Fin (edgeCount i + 1) → ℝ
  edge : ∀ i, Fin (edgeCount i) → SmoothEdge M
  edgeCount_pos : ∀ i, 0 < edgeCount i
  edge_injective : ∀ i k, InjOn (edge i k).map (Icc (0 : ℝ) 1)
  circle_boundary : ∀ p : centers,
    (⋃ i : Fin 2, ⋃ k, (edge (p, i) k).map '' Icc (0 : ℝ) 1) =
      frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) (p : M)).symm ''
        closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) (p : M) p) (radius p))
  edge_intersection : ∀ a b : Σ i, Fin (edgeCount i), a ≠ b →
    (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ∩ (edge b.1 b.2).map '' Icc (0 : ℝ) 1 ⊆
      {(edge a.1 a.2).map 0, (edge a.1 a.2).map 1} ∩
        {(edge b.1 b.2).map 0, (edge b.1 b.2).map 1}
  cut_strictMono : ∀ i, StrictMono (cut i) ∧ cut i 0 = 0 ∧
    cut i (Fin.last (edgeCount i)) = 1
  edge_map : ∀ i k t, (edge i k).map t =
    (chartAt (EuclideanSpace ℝ (Fin 2)) (i.1 : M)).symm
      (coordinateCircleArc (chartAt (EuclideanSpace ℝ (Fin 2)) (i.1 : M) i.1)
        (radius i.1) ((i.2 : ℝ) * Real.pi)
        (cut i k.castSucc + t * (cut i k.succ - cut i k.castSucc)))
  boundary_cover : (⋃ a : Σ i, Fin (edgeCount i),
    (edge a.1 a.2).map '' Icc (0 : ℝ) 1) = chartDiskBoundaryUnion centers radius
  finite_components :
    Finite (ConnectedComponents ((chartDiskBoundaryUnion centers radius)ᶜ : Set M))
  regions : Finset M
  regions_outside : ∀ x ∈ regions, x ∉ chartDiskBoundaryUnion centers radius
  regions_distinct : ∀ x ∈ regions, ∀ y ∈ regions,
    connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x =
      connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ y → x = y
  region_closure_cover :
    (⋃ x ∈ regions, closure (connectedComponentIn
      (chartDiskBoundaryUnion centers radius)ᶜ x)) = univ
  region_representative : ∀ x ∉ chartDiskBoundaryUnion centers radius,
    ∃ y : regions, connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x =
      connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ y
  region_containment : ∀ x ∉ chartDiskBoundaryUnion centers radius, ∃ p ∈ centers,
    connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (radius p) ∧
    closure (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
        closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (radius p) ∧
    IsCompact (closure (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x)) ∧
    closure (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source
  interior_edge_frontier : ∀ x ∉ chartDiskBoundaryUnion centers radius,
    ∃ (a : Σ i, Fin (edgeCount i)) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧
      (edge a.1 a.2).map t ∈
        frontier (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x) ∧
      ∀ b : Σ i, Fin (edgeCount i),
        (edge a.1 a.2).map t ≠ (edge b.1 b.2).map 0 ∧
          (edge a.1 a.2).map t ≠ (edge b.1 b.2).map 1
  regionLeft : (Σ i, Fin (edgeCount i)) → regions
  regionRight : (Σ i, Fin (edgeCount i)) → regions
  region_sides_distinct : ∀ a, regionLeft a ≠ regionRight a
  edge_interior_incidence : ∀ a, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : regions,
    (edge a.1 a.2).map t ∈
      frontier (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x) ↔
        x = regionLeft a ∨ x = regionRight a
  edge_region_incidence : ∀ a (x : regions),
    (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆
      frontier (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x) ↔
        x = regionLeft a ∨ x = regionRight a
  component_frontier : ∀ x : M,
    frontier (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x) =
      ⋃ a : {a : Σ i, Fin (edgeCount i) |
        (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆
          frontier (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x)},
        (edge a.val.1 a.val.2).map '' Icc (0 : ℝ) 1
  region_frontier : ∀ x : regions,
    frontier (connectedComponentIn (chartDiskBoundaryUnion centers radius)ᶜ x) =
      ⋃ a : {a : Σ i, Fin (edgeCount i) | x = regionLeft a ∨ x = regionRight a},
        (edge a.val.1 a.val.2).map '' Icc (0 : ℝ) 1

theorem exists_finite_chart_region_decomposition [CompactSpace M] :
    Nonempty (FiniteChartRegionDecomposition (M := M)) := by
  classical
  obtain ⟨s, r, hpos, htarget, hcover, hfinite, htriple, hregular⟩ :=
    exists_finite_chart_ball_cover_general_position (M := M)
  obtain ⟨n, c, edge, hn, hinj, hboundary, hmeet, hcuts, hmaps⟩ :=
    exists_parametrized_chart_disk_boundary_refinement_of_finite_intersections
      s r hpos htarget hfinite
  have hfinite_regions :=
    finite_regions_of_chart_circle_general_position s r hpos htarget hcover htriple hregular
  obtain ⟨regions, hregions_outside, hregions_distinct, hregions_cover⟩ :=
    exists_finite_region_closure_cover_of_chart_circle_general_position
      s r hpos htarget hcover htriple hregular
  have hregions := fun (x : M) (hx : x ∉ chartDiskBoundaryUnion s r) =>
    exists_chart_disk_containing_complementary_component s r hpos htarget hcover x hx
  have hboundary_cover : (⋃ p : Σ i, Fin (n i),
      (edge p.1 p.2).map '' Icc (0 : ℝ) 1) = chartDiskBoundaryUnion s r := by
    ext z
    simp only [chartDiskBoundaryUnion, mem_iUnion]
    constructor
    · rintro ⟨⟨⟨x, i⟩, k⟩, hz⟩
      refine ⟨x, x.property, ?_⟩
      rw [← hboundary x]
      exact mem_iUnion₂.mpr ⟨i, k, hz⟩
    · rintro ⟨x, hx, hz⟩
      rw [← hboundary ⟨x, hx⟩] at hz
      obtain ⟨i, k, hz⟩ := mem_iUnion₂.mp hz
      exact ⟨⟨(⟨x, hx⟩, i), k⟩, hz⟩
  have hregion_edge := fun (x : M) (hx : x ∉ chartDiskBoundaryUnion s r) =>
    exists_interior_edge_mem_frontier_complementary_component s r hpos htarget hcover
      (fun p : Σ i, Fin (n i) => (edge p.1 p.2).map) hboundary_cover x hx
  have hpair (a : Σ i, Fin (n i)) :
      ∃ u v : M, u ∉ chartDiskBoundaryUnion s r ∧ v ∉ chartDiskBoundaryUnion s r ∧
        connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ u ≠
          connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ v ∧
        ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : M,
          (edge a.1 a.2).map t ∈
              frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ↔
            connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x =
                connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ u ∨
              connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x =
                connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ v := by
    let p : s := a.1.1
    have hfrontier : frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) (p : M)).symm ''
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) (p : M) p) (r p)) =
        chartCircle (p : M) (r p) := by
      rw [frontier_chart_image (p : M) (isCompact_closedBall _ _) (htarget p p.property),
        frontier_closedBall _ (hpos p p.property).ne']
      rfl
    have hedge : (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆ chartCircle (p : M) (r p) := by
      rw [← hfrontier, ← hboundary p]
      exact fun z hz => mem_iUnion₂.mpr ⟨a.1.2, a.2, hz⟩
    have hcircle : chartCircle (p : M) (r p) ⊆ chartDiskBoundaryUnion s r := by
      rw [← hfrontier]
      exact fun z hz => mem_iUnion₂.mpr ⟨p, p.property, hz⟩
    have h := exists_exactly_two_incident_components_along_chartCircle_edge
      (fun b : Σ i, Fin (n i) => edge b.1 b.2) a (p : M) (p : M)
      (hinj a.1 a.2)
      (hedge.trans (chartCircle_subset_chart_source (p : M) (htarget p p.property)))
      (fun b hba z hz => (hmeet a b hba.symm hz).1) (hpos p p.property)
      (htarget p p.property) hedge (by rw [hboundary_cover]; exact hcircle)
    simpa only [hboundary_cover] using h
  choose incidentLeft incidentRight hleft hright hdistinct hincident using hpair
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  have hrepresentative (x : ((chartDiskBoundaryUnion s r)ᶜ : Set M)) :
      ∃ y : regions, connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x =
        connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ y := by
    obtain ⟨y, hy, hxy⟩ := Poincare.Topology.exists_component_representative_of_closure_cover
      (isClosed_chartDiskBoundaryUnion s r).isOpen_compl regions hregions_cover x.property
    exact ⟨⟨y, hy⟩, hxy⟩
  choose regionIndex hregionIndex using hrepresentative
  let regionLeft (a : Σ i, Fin (n i)) := regionIndex ⟨incidentLeft a, hleft a⟩
  let regionRight (a : Σ i, Fin (n i)) := regionIndex ⟨incidentRight a, hright a⟩
  have region_sides_distinct (a : Σ i, Fin (n i)) : regionLeft a ≠ regionRight a := by
    intro h
    apply hdistinct a
    exact (hregionIndex ⟨incidentLeft a, hleft a⟩).trans
      ((congrArg (fun y : regions => connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ y) h).trans
        (hregionIndex ⟨incidentRight a, hright a⟩).symm)
  have hclosed_incidence (a : Σ i, Fin (n i)) (x : M) :
      (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆
          frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ↔
        connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x =
            connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ (incidentLeft a) ∨
          connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x =
            connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ (incidentRight a) := by
    rw [(edge a.1 a.2).image_Icc_subset_closed_iff isClosed_frontier]
    constructor
    · intro h
      exact (hincident a (1 / 2) (by norm_num) x).mp (h ⟨1 / 2, by norm_num, rfl⟩)
    · rintro h z ⟨t, ht, rfl⟩
      exact (hincident a t ht x).mpr h
  have hregion_incidence (a : Σ i, Fin (n i)) (x : regions) :
      (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆
          frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ↔
        x = regionLeft a ∨ x = regionRight a := by
    rw [hclosed_incidence a x, hregionIndex ⟨incidentLeft a, hleft a⟩,
      hregionIndex ⟨incidentRight a, hright a⟩]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext (hregions_distinct x x.property (regionLeft a)
          (regionLeft a).property h))
      · exact Or.inr (Subtype.ext (hregions_distinct x x.property (regionRight a)
          (regionRight a).property h))
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hwhole_frontier (x : M) :
      frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) =
        ⋃ a : {a : Σ i, Fin (n i) | (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆
          frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x)},
          (edge a.val.1 a.val.2).map '' Icc (0 : ℝ) 1 := by
    have h := frontier_edge_complement_eq_iUnion_of_uniform_incidence
      (fun a : Σ i, Fin (n i) => edge a.1 a.2) (fun a => hinj a.1 a.2) x
      (fun a t ht hp => by
        rw [hboundary_cover] at hp ⊢
        exact (hclosed_incidence a x).mpr ((hincident a t ht x).mp hp))
    have hstatement := congrArg (fun K : Set M =>
      frontier (connectedComponentIn Kᶜ x) =
        ⋃ a : {a : Σ i, Fin (n i) | (edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆
          frontier (connectedComponentIn Kᶜ x)},
          (edge a.val.1 a.val.2).map '' Icc (0 : ℝ) 1) hboundary_cover
    exact hstatement ▸ h
  have hfinite_boundary (x : regions) :
      frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) =
        ⋃ a : {a : Σ i, Fin (n i) | x = regionLeft a ∨ x = regionRight a},
          (edge a.val.1 a.val.2).map '' Icc (0 : ℝ) 1 := by
    rw [hwhole_frontier x]
    ext z
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, hz⟩
      exact mem_iUnion.mpr ⟨⟨a.val, (hregion_incidence a.val x).mp a.property⟩, hz⟩
    · rintro ⟨_, ⟨a, rfl⟩, hz⟩
      exact mem_iUnion.mpr ⟨⟨a.val, (hregion_incidence a.val x).mpr a.property⟩, hz⟩
  refine ⟨{
    centers := s
    radius := r
    radius_pos := hpos
    closedBall_subset_target := htarget
    disk_cover := hcover
    circle_intersections_finite := hfinite
    no_triple := htriple
    circle_regular := hregular
    edgeCount := n
    cut := c
    edge := edge
    edgeCount_pos := hn
    edge_injective := hinj
    circle_boundary := hboundary
    edge_intersection := hmeet
    cut_strictMono := hcuts
    edge_map := hmaps
    boundary_cover := hboundary_cover
    finite_components := hfinite_regions
    regions := regions
    regions_outside := hregions_outside
    regions_distinct := hregions_distinct
    region_closure_cover := hregions_cover
    region_representative := fun x hx => ⟨regionIndex ⟨x, hx⟩, hregionIndex ⟨x, hx⟩⟩
    region_containment := hregions
    interior_edge_frontier := hregion_edge
    regionLeft := regionLeft
    regionRight := regionRight
    region_sides_distinct := region_sides_distinct
    edge_interior_incidence := ?_
    edge_region_incidence := hregion_incidence
    component_frontier := hwhole_frontier
    region_frontier := hfinite_boundary }⟩
  intro a t ht x
  rw [← hregion_incidence a x, hclosed_incidence a x]
  exact hincident a t ht x

end PoincareConjecture.Topology.Surface
