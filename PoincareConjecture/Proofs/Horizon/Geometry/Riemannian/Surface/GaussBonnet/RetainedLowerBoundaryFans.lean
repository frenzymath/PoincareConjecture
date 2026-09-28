import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapTipExclusion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.LowerArcFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.ChainJunctionFans








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in
theorem edge_point_mem_arrangement (e : T.decomposition.EdgeIndex) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (T.decomposition.edge e.1 e.2).map t ∈
      chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius := by
  rw [← T.decomposition.boundary_cover]
  exact mem_iUnion.mpr ⟨e, mem_image_of_mem _ ht⟩

omit [T2Space S] in


theorem band_contains_open_edge_point (e : T.decomposition.EdgeIndex) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (hq : (T.decomposition.edge e.1 e.2).map t ∈ (T.bands p i).faces.carrier) :
    p.1.2 = e ∧ t ∈ Icc ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ) := by
  have htrace : (T.decomposition.edge e.1 e.2).map t ∈
      (T.decomposition.edge p.1.2.1 p.1.2.2).map ''
        Icc ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ) := by
    rw [← T.band_boundary p i]
    exact ⟨hq, T.edge_point_mem_arrangement e (Ioo_subset_Icc_self ht)⟩
  obtain ⟨s, hs, hse⟩ := htrace
  have hsunit := (T.graphs p).piece_interval_unit i hs
  have he : p.1.2 = e := by
    by_contra hne
    have hmeet := (T.decomposition.edge_intersection p.1.2 e hne
      ⟨⟨s, Ioo_subset_Icc_self hsunit, hse⟩,
        mem_image_of_mem _ (Ioo_subset_Icc_self ht)⟩).1
    rcases hmeet with hzero | hone
    · have hsz := T.decomposition.edge_injective p.1.2.1 p.1.2.2
        (Ioo_subset_Icc_self hsunit) (by norm_num : (0 : ℝ) ∈ Icc 0 1) (hse.trans hzero)
      linarith [hsunit.1]
    · have hso := T.decomposition.edge_injective p.1.2.1 p.1.2.2
        (Ioo_subset_Icc_self hsunit) (by norm_num : (1 : ℝ) ∈ Icc 0 1) (hse.trans hone)
      linarith [hsunit.2]
  refine ⟨he, ?_⟩
  subst e
  have hst := T.decomposition.edge_injective p.1.2.1 p.1.2.2
    (Ioo_subset_Icc_self hsunit) (Ioo_subset_Icc_self ht) hse
  exact hst ▸ hs

omit [T2Space S] in
theorem core_parent_contribution_eq_zero_on_arrangement
    (g : RiemannianMetric 2 S) {q : S}
    (hq : q ∈ chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)
    (R : T.decomposition.regions) (t : (T.refined.mesh R).Triangle) :
    meshVertexAngleContribution g (T.parentCoordinates (.inr (.inr ⟨R, t⟩)))
      (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q = 0 := by
  apply meshVertexAngleContribution_eq_zero_of_not_mem_support
  rintro ⟨z, hz, hez⟩
  rw [(T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).support] at hz
  exact connectedComponentIn_subset _ _
    (T.refined.in_region R ⟨z, meshTriangleBasis_subset_support (T.refined.mesh R) t hz, hez⟩) hq

omit [T2Space S] in
theorem band_parent_contribution_eq_zero_off_interval
    (g : RiemannianMetric 2 S) (e : T.decomposition.EdgeIndex) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (hpi : ¬ (p.1.2 = e ∧ t ∈ Icc ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ)))
    (s : Fin (T.bands p i).faces.interface.count × Bool) :
    meshVertexAngleContribution g (T.parentCoordinates (.inr (.inl ⟨⟨p, i⟩, s⟩)))
      (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩)))
      ((T.decomposition.edge e.1 e.2).map t) = 0 := by
  apply meshVertexAngleContribution_eq_zero_of_not_mem_support
  intro hq
  rw [(T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).support] at hq
  change (T.decomposition.edge e.1 e.2).map t ∈
    (T.bands p i).faces.faceCoordinates s '' convexHull ℝ (range ((T.bands p i).faces.faceBasis s)) at hq
  rw [← (T.bands p i).faces.face_carrier_eq_coordinates s] at hq
  exact hpi (T.band_contains_open_edge_point e ht p i (mem_iUnion.mpr ⟨s, hq⟩))

omit [T2Space S] in
theorem band_bottom_vertices_eq_edge (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count) :
    (T.bands p i).faces.vertex (0, false) =
        (T.decomposition.edge p.1.2.1 p.1.2.2).map ((T.graphs p).cut i.castSucc) ∧
      (T.bands p i).faces.vertex (Fin.last (T.bands p i).faces.interface.count, false) =
        (T.decomposition.edge p.1.2.1 p.1.2.2).map ((T.graphs p).cut i.succ) := by
  constructor
  · have h := (T.bands p i).left_endpoint_coordinate_start ((T.graphs p).cut_lt i).le
    rw [(T.bands p i).faces.face_corner_eq_vertex] at h
    exact h
  · have h := (T.bands p i).right_endpoint_coordinate_start ((T.graphs p).cut_lt i).le
    rw [(T.bands p i).faces.face_corner_eq_vertex] at h
    change (T.bands p i).faces.vertex ((T.bands p i).faces.lastCell.succ, false) = _ at h
    have hl : (T.bands p i).faces.lastCell.succ =
        Fin.last (T.bands p i).faces.interface.count := by
      apply Fin.ext
      have hn := (T.bands p i).faces.interface.count_pos
      simp only [ObliqueBandFaces.lastCell, Fin.val_succ, Fin.val_last]
      omega
    rwa [hl] at h



theorem band_lower_open_contribution (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {t : ℝ} (ht : t ∈ Ioo ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ))
    (hpoint : (T.decomposition.edge p.1.2.1 p.1.2.2).map t = q.1) :
    (∑ s : Fin (T.bands p i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates s)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))) q.1) = Real.pi := by
  have heq (s : Fin (T.bands p i).faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩)) =
        (TriangleMesh.single ((T.bands p i).faces.faceBasis s)
          ((T.bands p i).faces.faceBasis s).ind).refineByLines
            (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).mesh_eq_refineByLines
  have hqarc : q.1 ∈ (T.bands p i).faces.lowerArc := by
    rw [(T.chains p).lowerArc_eq_original (T.bands p) i]
    exact ⟨t, Ioo_subset_Icc_self ht, hpoint⟩
  have hqcarrier : q.1 ∈ (T.bands p i).faces.carrier :=
    (T.bands p i).faces.isClosed_carrier.frontier_subset
      ((T.bands p i).faces.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inl hqarc))))
  obtain ⟨s, hs⟩ := mem_iUnion.mp hqcarrier
  have hused := T.parent_mesh_vertex_is_used q (.inr (.inl ⟨⟨p, i⟩, s⟩)) (by
    change q.1 ∈ (T.bands p i).faces.faceCoordinates s ''
      (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))).toPlaneComplex.support
    rw [(T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).support]
    exact (T.bands p i).faces.face_carrier_eq_coordinates s ▸ hs)
  have hcoord := linearGraphCoordinates_contMDiff
    (chartAt Plane (T.chart p.1.1 : S)).symm ((T.graphs p).piece i).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞)) (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  simp_rw [heq]
  apply (T.bands p i).faces.lower_arc_refined_vertex_fan g hcoord.1 hcoord.2 _ hqarc
  · intro h
    rw [(T.band_bottom_vertices_eq_edge p i).1, ← hpoint] at h
    have htunit := (T.graphs p).piece_interval_unit i (Ioo_subset_Icc_self ht)
    have he := T.decomposition.edge_injective p.1.2.1 p.1.2.2
      (Ioo_subset_Icc_self htunit) (Ioo_subset_Icc_self ((T.graphs p).cut_mem i.castSucc)) h
    exact ht.1.ne' he
  · intro h
    rw [(T.band_bottom_vertices_eq_edge p i).2, ← hpoint] at h
    have htunit := (T.graphs p).piece_interval_unit i (Ioo_subset_Icc_self ht)
    have he := T.decomposition.edge_injective p.1.2.1 p.1.2.2
      (Ioo_subset_Icc_self htunit) (Ioo_subset_Icc_self ((T.graphs p).cut_mem i.succ)) h
    exact ht.2.ne he
  · refine ⟨s, ?_⟩
    rw [heq s] at hused
    exact hused

omit [T2Space S] in


theorem band_lower_junction_contribution (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) :
    (∑ s : Fin (T.bands p i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates s)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩)))
        ((T.decomposition.edge p.1.2.1 p.1.2.2).map ((T.graphs p).cut i.succ))) +
    (∑ s : Fin (T.bands p j).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p j).faces.faceCoordinates s)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, j⟩, s⟩)))
        ((T.decomposition.edge p.1.2.1 p.1.2.2).map ((T.graphs p).cut i.succ))) = Real.pi := by
  have heq (k : Fin (T.graphs p).count) (s : Fin (T.bands p k).faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, k⟩, s⟩)) =
        (TriangleMesh.single ((T.bands p k).faces.faceBasis s)
          ((T.bands p k).faces.faceBasis s).ind).refineByLines
            (T.refinement.subdivision (.inr (.inl ⟨⟨p, k⟩, s⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, k⟩, s⟩))).mesh_eq_refineByLines
  simp_rw [heq]
  exact (T.chains p).adjacent_bottom_refined_fan (T.bands p)
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞)) (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    g (fun k s => (T.refinement.subdivision (.inr (.inl ⟨⟨p, k⟩, s⟩))).refinement_lines) i j hij

omit [T2Space S] in
private theorem cut_interval_unique_of_open (p : T.decomposition.IncidentEdgeIndex)
    {i j : Fin (T.graphs p).count} {t : ℝ}
    (hi : t ∈ Ioo ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ))
    (hj : t ∈ Icc ((T.graphs p).cut j.castSucc) ((T.graphs p).cut j.succ)) : j = i := by
  rcases lt_trichotomy j i with hji | hji | hij
  · have hle : j.succ ≤ i.castSucc := hji
    exact False.elim (not_lt_of_ge (hj.2.trans ((T.graphs p).cut_strictMono.monotone hle)) hi.1)
  · exact hji
  · have hle : i.succ ≤ j.castSucc := hij
    exact False.elim (not_lt_of_ge (((T.graphs p).cut_strictMono.monotone hle).trans hj.1) hi.2)



theorem band_side_contribution_on_open_trimmed_edge (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {t : ℝ} (ht : t ∈ Ioo (T.cut p.1.2 false) (1 - T.cut p.1.2 true))
    (hpoint : (T.decomposition.edge p.1.2.1 p.1.2.2).map t = q.1) :
    (∑ i : Fin (T.graphs p).count,
      ∑ s : Fin (T.bands p i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates s)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))) q.1) = Real.pi := by
  let b := fun i : Fin (T.graphs p).count =>
    ∑ s : Fin (T.bands p i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates s)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))) q.1
  have htunit : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨(T.cut_mem p.1.2 false).1.trans ht.1, by linarith [(T.cut_mem p.1.2 true).1, ht.2]⟩
  have hoff (i : Fin (T.graphs p).count)
      (hi : t ∉ Icc ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ)) : b i = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [← hpoint]
    exact T.band_parent_contribution_eq_zero_off_interval g p.1.2 htunit p i
      (fun h => hi h.2) s
  change (∑ i, b i) = Real.pi
  by_cases hcut : ∃ k : Fin ((T.graphs p).count + 1), (T.graphs p).cut k = t
  · obtain ⟨k, hk⟩ := hcut
    have hkpos : 0 < k.val := by
      have h : (0 : Fin ((T.graphs p).count + 1)) < k := (T.graphs p).cut_strictMono.lt_iff_lt.mp
        (by simpa only [(T.graphs p).cut_first, hk] using ht.1)
      exact h
    have hklt : k.val < (T.graphs p).count := by
      have h : k < Fin.last (T.graphs p).count := (T.graphs p).cut_strictMono.lt_iff_lt.mp
        (by simpa only [(T.graphs p).cut_last, hk] using ht.2)
      exact h
    let i : Fin (T.graphs p).count := ⟨k.val - 1, by omega⟩
    let j : Fin (T.graphs p).count := ⟨k.val, hklt⟩
    have hi : i.succ = k := by apply Fin.ext; simp only [i, Fin.val_succ]; omega
    have hj : j.castSucc = k := Fin.ext rfl
    have hij : i ≠ j := by intro h; have hval := congrArg Fin.val h; dsimp [i, j] at hval; omega
    have hsupport : (∑ m, b m) = ∑ m ∈ ({i, j} : Finset (Fin (T.graphs p).count)), b m := by
      symm
      apply Finset.sum_subset (by simp)
      intro m _ hm
      apply hoff
      intro hmcut
      have hmlo : m.castSucc ≤ k := (T.graphs p).cut_strictMono.le_iff_le.mp (hk ▸ hmcut.1)
      have hmhi : k ≤ m.succ := (T.graphs p).cut_strictMono.le_iff_le.mp (hk ▸ hmcut.2)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      have hmi : m.val ≠ i.val := fun h => hm.1 (Fin.ext h)
      have hmj : m.val ≠ j.val := fun h => hm.2 (Fin.ext h)
      change m.val ≤ k.val at hmlo
      change k.val ≤ m.val + 1 at hmhi
      dsimp only [i, j] at hmi hmj
      omega
    rw [hsupport, Finset.sum_pair hij]
    have hfan := T.band_lower_junction_contribution g p i j (hi.trans hj.symm)
    simpa only [hi, hk, hpoint] using hfan
  · have hcover := iUnion_Icc_consecutive (T.graphs p).count_pos
        (T.graphs p).cut (T.graphs p).cut_strictMono.monotone
    rw [(T.graphs p).cut_first, (T.graphs p).cut_last] at hcover
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ Ioo_subset_Icc_self ht)
    have hio : t ∈ Ioo ((T.graphs p).cut i.castSucc) ((T.graphs p).cut i.succ) :=
      ⟨lt_of_le_of_ne hi.1 (fun h => hcut ⟨i.castSucc, h⟩),
        lt_of_le_of_ne hi.2 (fun h => hcut ⟨i.succ, h.symm⟩)⟩
    rw [Finset.sum_eq_single i]
    · exact T.band_lower_open_contribution g p i q hio hpoint
    · intro j _ hji
      exact hoff j (fun hj => hji (T.cut_interval_unique_of_open p hio hj))
    · simp

set_option maxHeartbeats 1600000 in



theorem canonical_vertex_fan_on_open_trimmed_edge_of_not_mem_caps
    (g : RiemannianMetric 2 S) (e : T.decomposition.EdgeIndex)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {t : ℝ} (ht : t ∈ Ioo (T.cut e false) (1 - T.cut e true))
    (hpoint : (T.decomposition.edge e.1 e.2).map t = q.1)
    (hcap : ∀ (v : T.decomposition.vertices) (s : Bool × Bool),
      q.1 ∉ ((T.caps v).face s).carrier) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  let f : T.Parent → ℝ := fun i =>
    meshVertexAngleContribution g (T.parentCoordinates i) (T.refinement.mesh i) q.1
  let b := fun (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) =>
    ∑ s : Fin (T.bands p i).faces.interface.count × Bool, f (.inr (.inl ⟨⟨p, i⟩, s⟩))
  have htunit : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨(T.cut_mem e false).1.trans ht.1, by linarith [(T.cut_mem e true).1, ht.2]⟩
  have hcaps : (∑ a : T.decomposition.vertices × (Bool × Bool), f (.inl a)) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨v, s⟩ _
    apply meshVertexAngleContribution_eq_zero_of_not_mem_support
    intro hq
    rw [(T.refinement.subdivision (.inl (v, s))).support] at hq
    exact hcap v s ((T.caps v).carrier_eq s ▸ hq)
  have hbands : (∑ side : Bool, ∑ i : Fin (T.graphs (T.incidentSide e side)).count,
      b (T.incidentSide e side) i) =
      ∑ p : T.decomposition.IncidentEdgeIndex, ∑ i : Fin (T.graphs p).count, b p i := by
    apply Fintype.sum_of_injective (T.incidentSide e) (T.incidentSide_injective e)
    · intro p hp
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro s _
      change meshVertexAngleContribution g _ _ q.1 = 0
      rw [← hpoint]
      apply T.band_parent_contribution_eq_zero_off_interval g e htunit p i _ s
      exact fun h => hp (T.exists_incidentSide_of_edge_eq e p h.1)
    · intro side
      rfl
  have hside (side : Bool) : (∑ i : Fin (T.graphs (T.incidentSide e side)).count,
      b (T.incidentSide e side) i) = Real.pi :=
    T.band_side_contribution_on_open_trimmed_edge g (T.incidentSide e side) q ht hpoint
  have hcores : (∑ a : Σ R : T.decomposition.regions, (T.refined.mesh R).Triangle,
      f (.inr (.inr a))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact T.core_parent_contribution_eq_zero_on_arrangement g
      (hpoint ▸ T.edge_point_mem_arrangement e (Ioo_subset_Icc_self htunit)) a.1 a.2
  rw [T.vertex_contribution_eq_parent_sum]
  change (∑ i : T.Parent, f i) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hcaps, hcores, zero_add, add_zero]
  have hband_sum :
      (∑ a : Σ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
        Fin (T.bands a.1 a.2).faces.interface.count × Bool, f (.inr (.inl a))) =
      ∑ side : Bool, ∑ i : Fin (T.graphs (T.incidentSide e side)).count,
        b (T.incidentSide e side) i := by
    rw [Fintype.sum_sigma]
    change (∑ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs, b a.1 a.2) = _
    rw [Fintype.sum_sigma]
    exact hbands.symm
  rw [hband_sum]
  simp_rw [hside]
  simp only [Fintype.sum_bool]
  ring

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
