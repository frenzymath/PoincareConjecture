import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapTipFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.IndependentFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in
theorem cap_tip_parameter_mem (e : T.decomposition.EdgeIndex) (terminal : Bool) :
    (if terminal then 1 - T.cut e terminal else T.cut e terminal) ∈ Ioo (0 : ℝ) 1 := by
  have h := T.cut_mem e terminal
  cases terminal <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [h.1, h.2]

omit [T2Space S] in
theorem cap_tip_mem_arrangement (e : T.decomposition.EdgeIndex) (terminal : Bool) :
    T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal) ∈
      chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius := by
  rw [← T.decomposition.boundary_cover]
  apply mem_iUnion.mpr
  exact ⟨e, mem_image_of_mem _ (Ioo_subset_Icc_self (T.cap_tip_parameter_mem e terminal))⟩

omit [T2Space S] in

theorem band_contains_cap_tip (e : T.decomposition.EdgeIndex) (terminal : Bool)
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (hq : T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal) ∈
      (T.bands p i).faces.carrier) :
    p.1.2 = e ∧ (if terminal then i = (T.graphs p).lastPiece else i = (T.graphs p).firstPiece) := by
  have hboundary := T.cap_tip_mem_arrangement e terminal
  have hband : T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal) ∈
      (T.decomposition.edge p.1.2.1 p.1.2.2).map ''
        Icc ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ) := by
    rw [← T.band_boundary p i]
    exact ⟨hq, hboundary⟩
  obtain ⟨t, ht, hte⟩ := hband
  have htunit := (T.graphs p).piece_interval_unit i ht
  have he : p.1.2 = e := by
    by_contra hne
    have hmeet := (T.decomposition.edge_intersection p.1.2 e hne
      ⟨⟨t, Ioo_subset_Icc_self htunit, hte⟩,
        mem_image_of_mem _ (Ioo_subset_Icc_self (T.cap_tip_parameter_mem e terminal))⟩).1
    rcases hmeet with hzero | hone
    · have htz := T.decomposition.edge_injective p.1.2.1 p.1.2.2
        (Ioo_subset_Icc_self htunit) (by norm_num : (0 : ℝ) ∈ Icc 0 1) (hte.trans hzero)
      linarith [htunit.1]
    · have hto := T.decomposition.edge_injective p.1.2.1 p.1.2.2
        (Ioo_subset_Icc_self htunit) (by norm_num : (1 : ℝ) ∈ Icc 0 1) (hte.trans hone)
      linarith [htunit.2]
  refine ⟨he, ?_⟩
  subst e
  have htparam : t = if terminal then 1 - T.cut p.1.2 terminal else T.cut p.1.2 terminal :=
    T.decomposition.edge_injective p.1.2.1 p.1.2.2 (Ioo_subset_Icc_self htunit)
      (Ioo_subset_Icc_self (T.cap_tip_parameter_mem p.1.2 terminal)) hte
  rw [htparam] at ht
  cases terminal
  · simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢
    have hcut : (T.graphs p).cut i.castSucc = (T.graphs p).cut 0 :=
      le_antisymm (by simpa only [(T.graphs p).cut_first] using ht.1)
        ((T.graphs p).cut_strictMono.monotone (Fin.zero_le _))
    have hi := (T.graphs p).cut_strictMono.injective hcut
    apply Fin.ext
    simpa only [Fin.val_castSucc, Fin.val_zero,
      FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.firstPiece] using congrArg Fin.val hi
  · simp only [↓reduceIte] at ht ⊢
    have hcut : (T.graphs p).cut i.succ = (T.graphs p).cut (Fin.last (T.graphs p).count) :=
      le_antisymm ((T.graphs p).cut_strictMono.monotone (Fin.le_last _))
        (by simpa only [(T.graphs p).cut_last] using ht.2)
    have hi := (T.graphs p).cut_strictMono.injective hcut
    apply Fin.ext
    have hiv := congrArg Fin.val hi
    change i.val = (T.graphs p).count - 1
    simp only [Fin.val_succ, Fin.val_last] at hiv
    omega

omit [T2Space S] in

theorem core_parent_contribution_eq_zero_at_cap_tip (g : RiemannianMetric 2 S)
    (e : T.decomposition.EdgeIndex) (terminal : Bool) (R : T.decomposition.regions)
    (t : (T.refined.mesh R).Triangle) :
    meshVertexAngleContribution g (T.parentCoordinates (.inr (.inr ⟨R, t⟩)))
      (T.refinement.mesh (.inr (.inr ⟨R, t⟩)))
      (T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal)) = 0 := by
  apply meshVertexAngleContribution_eq_zero_of_not_mem_support
  rintro ⟨z, hz, hez⟩
  rw [(T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).support] at hz
  have hregion := T.refined.in_region R
    ⟨z, meshTriangleBasis_subset_support (T.refined.mesh R) t hz, hez⟩
  exact connectedComponentIn_subset _ _ hregion (T.cap_tip_mem_arrangement e terminal)

omit [T2Space S] in
theorem incidentSide_injective (e : T.decomposition.EdgeIndex) :
    Function.Injective (T.incidentSide e) := by
  intro a b h
  have hh := congrArg (fun p : T.decomposition.IncidentEdgeIndex => p.1.1) h
  cases a <;> cases b <;> simp_all [incidentSide, T.decomposition.region_sides_distinct e,
    (T.decomposition.region_sides_distinct e).symm]

omit [T2Space S] in
theorem exists_incidentSide_of_edge_eq (e : T.decomposition.EdgeIndex)
    (p : T.decomposition.IncidentEdgeIndex) (he : p.1.2 = e) :
    ∃ side, T.incidentSide e side = p := by
  rcases p.2 with hleft | hright
  · refine ⟨true, Subtype.ext (Prod.ext ?_ he.symm)⟩
    simpa only [incidentSide, ↓reduceIte, he] using hleft.symm
  · refine ⟨false, Subtype.ext (Prod.ext ?_ he.symm)⟩
    simpa only [incidentSide, Bool.false_eq_true, ↓reduceIte, he] using hright.symm

theorem cap_tip_mem_original_cap (e : T.decomposition.EdgeIndex) (terminal : Bool) :
    ∃ s : Bool × Bool, T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal) ∈
      ((T.caps (T.decomposition.edgeEndpoint e terminal)).face s).carrier := by
  cases terminal
  · exact ⟨(T.leftCap (T.incidentSide e false)).sector,
      (T.leftCap (T.incidentSide e false)).tip_mem_cap⟩
  · exact ⟨(T.rightCap (T.incidentSide e false)).sector,
      (T.rightCap (T.incidentSide e false)).tip_mem_cap⟩

theorem cap_parent_contribution_eq_zero_at_other_cap_tip (g : RiemannianMetric 2 S)
    (e : T.decomposition.EdgeIndex) (terminal : Bool) (p : T.decomposition.vertices)
    (hp : p ≠ T.decomposition.edgeEndpoint e terminal) (s : Bool × Bool) :
    meshVertexAngleContribution g (T.parentCoordinates (.inl (p, s)))
      (T.refinement.mesh (.inl (p, s)))
      (T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal)) = 0 := by
  apply meshVertexAngleContribution_eq_zero_of_not_mem_support
  intro hq
  rw [(T.refinement.subdivision (.inl (p, s))).support] at hq
  change T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal) ∈
    (T.caps p).coordinates s '' convexHull ℝ (range (rightTriangleBasis (T.caps p).scale_pos)) at hq
  rw [← (T.caps p).carrier_eq s] at hq
  obtain ⟨t, ht⟩ := T.cap_tip_mem_original_cap e terminal
  exact disjoint_left.mp (T.caps_disjoint_of_vertices_ne p _ hp s t) hq ht

omit [T2Space S] in

theorem band_parent_contribution_eq_zero_at_other_cap_tip (g : RiemannianMetric 2 S)
    (e : T.decomposition.EdgeIndex) (terminal : Bool)
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (hpi : ¬ (p.1.2 = e ∧
      (if terminal then i = (T.graphs p).lastPiece else i = (T.graphs p).firstPiece)))
    (s : Fin (T.bands p i).faces.interface.count × Bool) :
    meshVertexAngleContribution g (T.parentCoordinates (.inr (.inl ⟨⟨p, i⟩, s⟩)))
      (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩)))
      (T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal)) = 0 := by
  apply meshVertexAngleContribution_eq_zero_of_not_mem_support
  intro hq
  rw [(T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).support] at hq
  change T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal) ∈
    (T.bands p i).faces.faceCoordinates s '' convexHull ℝ (range ((T.bands p i).faces.faceBasis s)) at hq
  rw [← (T.bands p i).faces.face_carrier_eq_coordinates s] at hq
  exact hpi (T.band_contains_cap_tip e terminal p i (mem_iUnion.mpr ⟨s, hq⟩))

set_option maxHeartbeats 800000 in

theorem vertex_fan_at_cap_tip (g : RiemannianMetric 2 S)
    (e : T.decomposition.EdgeIndex) (terminal : Bool) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis
      (T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal)) = 2 * Real.pi := by
  let q := T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal)
  let f : T.Parent → ℝ := fun i =>
    meshVertexAngleContribution g (T.parentCoordinates i) (T.refinement.mesh i) q
  let j := fun p : T.decomposition.IncidentEdgeIndex =>
    if terminal then (T.graphs p).lastPiece else (T.graphs p).firstPiece
  let b := fun (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) =>
    ∑ s : Fin (T.bands p i).faces.interface.count × Bool, f (.inr (.inl ⟨⟨p, i⟩, s⟩))
  have hcaps : (∑ a : T.decomposition.vertices × (Bool × Bool), f (.inl a)) =
      ∑ s : Bool × Bool, f (.inl (T.decomposition.edgeEndpoint e terminal, s)) := by
    rw [Fintype.sum_prod_type]
    apply Fintype.sum_eq_single (T.decomposition.edgeEndpoint e terminal)
    intro p hp
    apply Finset.sum_eq_zero
    intro s _
    exact T.cap_parent_contribution_eq_zero_at_other_cap_tip g e terminal p hp s
  have hpiece (p : T.decomposition.IncidentEdgeIndex) :
      (∑ i : Fin (T.graphs p).count, b p i) = b p (j p) := by
    apply Fintype.sum_eq_single (j p)
    intro i hi
    apply Finset.sum_eq_zero
    intro s _
    apply T.band_parent_contribution_eq_zero_at_other_cap_tip g e terminal p i _ s
    intro h
    apply hi
    cases terminal <;> simpa only [j, Bool.false_eq_true, ↓reduceIte] using h.2
  have hbands : (∑ side : Bool, b (T.incidentSide e side) (j (T.incidentSide e side))) =
      ∑ p : T.decomposition.IncidentEdgeIndex, ∑ i : Fin (T.graphs p).count, b p i := by
    apply Fintype.sum_of_injective (T.incidentSide e) (T.incidentSide_injective e)
    · intro p hp
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro s _
      apply T.band_parent_contribution_eq_zero_at_other_cap_tip g e terminal p i _ s
      intro h
      exact hp (T.exists_incidentSide_of_edge_eq e p h.1)
    · intro side
      exact (hpiece _).symm
  have hcores : (∑ a : Σ R : T.decomposition.regions, (T.refined.mesh R).Triangle,
      f (.inr (.inr a))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact T.core_parent_contribution_eq_zero_at_cap_tip g e terminal a.1 a.2
  rw [T.vertex_contribution_eq_parent_sum]
  change (∑ i : T.Parent, f i) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hcores, add_zero, hcaps]
  have hband_sum :
      (∑ a : Σ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
        Fin (T.bands a.1 a.2).faces.interface.count × Bool, f (.inr (.inl a))) =
      ∑ side : Bool, b (T.incidentSide e side) (j (T.incidentSide e side)) := by
    rw [Fintype.sum_sigma]
    change (∑ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      b a.1 a.2) = _
    rw [Fintype.sum_sigma]
    exact hbands.symm
  rw [hband_sum, Fintype.sum_prod_type]
  cases terminal
  · exact T.first_cap_tip_contribution g e
  · exact T.last_cap_tip_contribution g e

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
