


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Sectors
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.EdgeIntersections









set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in


theorem vertex_cap_interior_subset_sector
    {p : M} {P : ChartCircleArrangementVertexPatch D.radius p}
    {x : Bool × Bool → M} (B : ChartCircleArrangementVertexPatch.VertexCapFaces P x)
    (i : Bool × Bool) : interior (B.face i).carrier ⊆ P.sector i := by
  intro q hq
  rcases B.carrier_subset_sector_sides i (interior_subset hq) with hsector | hside
  · exact hsector
  · exfalso
    apply disjoint_left.mp disjoint_interior_frontier hq
    rcases hside with hfirst | hsecond
    · rw [← B.first_image i] at hfirst
      exact (B.face i).boundary_image_subset_frontier 2 hfirst
    · rw [← B.second_image i] at hsecond
      exact (B.face i).boundary_image_subset_frontier 1 hsecond



theorem exists_region_vertex_caps :
    ∃ (chart : D.regions → D.centers)
      (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
      (region : D.vertices → Bool × Bool → D.regions)
      (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
        (fun i => (chart (region p i) : M)))
      (cut : D.EdgeIndex → Bool → ℝ),
      (∀ x : D.regions, closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart x : M)).source) ∧
      (∀ p, (P p).centers ⊆ (D.centers : Set M)) ∧
      (∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier) ∧
      (∀ (p : D.vertices) (a : D.EdgeIndex),
        (p : M) ∉ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 →
        Disjoint (P p).carrier ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1)) ∧
      (∀ p q, q ∈ (P p).carrier →
        (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles)) ∧
      (∀ p i, (P p).sector i ⊆ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)) ∧
      (∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) ∧
      (∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) ∧
      (∀ p q, p ≠ q → ∀ i j, Disjoint ((B p).face i).carrier ((B q).face j).carrier) ∧
      (∀ (a : D.EdgeIndex) (terminal : Bool), cut a terminal ∈ Ioo (0 : ℝ) (1 / 3) ∧
        ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
          (((B (D.edgeEndpoint a terminal)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
            D.edgeFromEndpoint a terminal '' Icc 0 (cut a terminal) ∧
          (((B (D.edgeEndpoint a terminal)).face j).boundary k).map '' Icc (0 : ℝ) 1 =
            D.edgeFromEndpoint a terminal '' Icc 0 (cut a terminal) ∧
          ∀ s, s = i ∨ s = j →
            (((B (D.edgeEndpoint a terminal)).face s).boundary k).map 0 =
              (D.edgeEndpoint a terminal : M) ∧
            (((B (D.edgeEndpoint a terminal)).face s).boundary k).map 1 =
              D.edgeFromEndpoint a terminal (cut a terminal) ∧
            ∃ A : OpenPartialHomeomorph ℝ ℝ,
              A (B (D.edgeEndpoint a terminal)).scale = cut a terminal ∧
              Icc 0 (B (D.edgeEndpoint a terminal)).scale ⊆ A.source ∧
              StrictMonoOn A A.source ∧ ContDiffOn ℝ ∞ A A.source ∧
              ContDiffOn ℝ ∞ A.symm A.target ∧
              ∀ u ∈ Icc 0 (B (D.edgeEndpoint a terminal)).scale,
                D.edgeFromEndpoint a terminal (A u) =
                  (P (D.edgeEndpoint a terminal)).sectorCoordinates s
                    (if k = 1 then (0, u) else (u, 0))) ∧
      (∀ a, (⋃ p, ⋃ i, ((B p).face i).carrier) ∩ D.middleArc cut a =
        {(D.edge a.1 a.2).map (cut a false),
          (D.edge a.1 a.2).map (1 - cut a true)}) ∧
      (∀ a, Disjoint (⋃ p, ⋃ i, ((B p).face i).carrier)
        ((D.edge a.1 a.2).map '' Ioo (cut a false) (1 - cut a true))) ∧
      ∃ N : Set M, IsOpen N ∧ (D.vertices : Set M) ⊆ N ∧
        N ⊆ ⋃ p, ⋃ i, ((B p).face i).carrier := by
  classical
  choose x hx hregion hclosed hcompact hchart using
    fun q : D.regions => D.region_containment q (D.regions_outside q q.property)
  let chart (q : D.regions) : D.centers := ⟨x q, hx q⟩
  obtain ⟨P, region, hcenters, hdisjoint, havoid, hlocal, hsector, hsectors, _, _⟩ :=
    D.exists_vertex_patches_with_regions
  have hcharts (p : D.vertices) (i : Bool × Bool) : (P p).closedSector i ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart (region p i) : M)).source :=
    (hsectors p i).trans (hchart (region p i))
  obtain ⟨ε, B, cut, hε, hscale, hmatch⟩ := D.exists_vertex_caps_matching_edges
    P hlocal (fun p i => (chart (region p i) : M)) hcharts
  have hcut := fun a b => (hmatch a b).1
  have hradial (a : D.EdgeIndex) (b : Bool) : ∃ d : Bool × Bool,
      (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b) := by
    obtain ⟨i, j, k, _, hk, hi, _⟩ := (hmatch a b).2
    exact (B (D.edgeEndpoint a b)).exists_radialSide_eq_of_boundary_match i k hk hi
  refine ⟨chart, P, region, B, cut, hchart, hcenters, hdisjoint, havoid, hlocal,
    hsector, hsectors, ?_, ?_, hmatch,
    D.vertex_caps_inter_middleArc P B hdisjoint hlocal cut hcut hradial,
    D.vertex_caps_disjoint_open_middleArc P B hdisjoint hlocal cut hcut hradial, ?_⟩
  · intro p i
    exact ((B p).carrier_subset_sector i).trans (hsectors p i)
  · intro p q hpq i j
    exact (hdisjoint p q hpq).mono ((B p).carrier_subset_patch i)
      ((B q).carrier_subset_patch j)
  · refine ⟨⋃ p, (B p).neighborhood, isOpen_iUnion (fun p => (B p).isOpen_neighborhood), ?_, ?_⟩
    · intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, (B ⟨p, hp⟩).mem_neighborhood⟩
    · intro q hq
      obtain ⟨p, hp⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨p, (B p).neighborhood_subset_carriers hp⟩



theorem vertex_caps_intersection
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    {a b : D.vertices × (Bool × Bool)} (hab : a ≠ b) :
    ((B a.1).face a.2).carrier ∩ ((B b.1).face b.2).carrier = ∅ ∨
      (∃ k : Fin 3,
        ((B a.1).face a.2).carrier ∩ ((B b.1).face b.2).carrier =
          (((B a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 ∧
        (((B a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 =
          (((B b.1).face b.2).boundary k).map '' Icc (0 : ℝ) 1) ∨
      ((B a.1).face a.2).carrier ∩ ((B b.1).face b.2).carrier = {(a.1 : M)} := by
  rcases a with ⟨p, i⟩
  rcases b with ⟨q, j⟩
  by_cases hpq : p = q
  · subst q
    exact Or.inr ((B p).intersection_edge_or_vertex (fun hij => hab (Prod.ext rfl hij)))
  · exact Or.inl (Set.disjoint_iff_inter_eq_empty.mp
      ((hdisjoint p q hpq).mono ((B p).carrier_subset_patch i)
        ((B q).carrier_subset_patch j)))

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
