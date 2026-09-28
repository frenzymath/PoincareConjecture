import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAttachmentGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCoreSectors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedInteriorFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapChordHalfspaces
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshSubfamilyContribution








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

private theorem cap_chord_avoidance_germ
    (p : T.decomposition.vertices) (s : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier) :
    ∀ᶠ z in 𝓝 ((((T.caps p).face s).boundary 0).map t),
      (∀ a : T.decomposition.vertices × (Bool × Bool), a ≠ (p, s) →
        z ∉ ((T.caps a.1).face a.2).carrier) ∧
      (∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
        z ∉ (T.bands a.1 a.2).faces.carrier) := by
  have hc : ∀ᶠ z in 𝓝 ((((T.caps p).face s).boundary 0).map t),
      ∀ a : T.decomposition.vertices × (Bool × Bool), a ≠ (p, s) →
        z ∉ ((T.caps a.1).face a.2).carrier := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : a = (p, s)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h ha))
    · have hn : (((T.caps p).face s).boundary 0).map t ∉
          ((T.caps a.1).face a.2).carrier := by
        intro h
        have he := T.cap_unique_at_open_chord p s ht a.1 a.2 h
        exact ha (Prod.ext he.1 he.2)
      filter_upwards [((T.caps a.1).face a.2).isClosed_carrier.isOpen_compl.mem_nhds hn]
        with z hz
      exact fun _ => hz
  have hb : ∀ᶠ z in 𝓝 ((((T.caps p).face s).boundary 0).map t),
      ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
        z ∉ (T.bands a.1 a.2).faces.carrier := by
    apply Filter.eventually_all.mpr
    intro a
    exact (T.bands a.1 a.2).faces.isClosed_carrier.isOpen_compl.mem_nhds (hband a)
  exact hc.and hb



theorem exists_core_at_open_cap_chord
    (p : T.decomposition.vertices) (s : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier) :
    ∃ R : T.decomposition.regions,
      (((T.caps p).face s).boundary 0).map t ∈
        (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support := by
  by_contra hn
  push Not at hn
  have hcore : ∀ᶠ z in 𝓝 ((((T.caps p).face s).boundary 0).map t),
      ∀ R : T.decomposition.regions, z ∉
        (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support := by
    apply Filter.eventually_all.mpr
    intro R
    have hc : IsClosed ((chartAt Plane (T.chart R : S)).symm ''
        (T.refined.mesh R).toPlaneComplex.support) := by
      rw [T.refined_core_back R]
      exact isClosed_closure
    exact hc.isOpen_compl.mem_nhds (hn R)
  have hint : ((T.caps p).face s).carrier ∈
      𝓝 ((((T.caps p).face s).boundary 0).map t) := by
    filter_upwards [T.cap_chord_avoidance_germ p s ht hband, hcore] with z hz hzcore
    have hcover : z ∈ ⋃ R ∈ T.decomposition.regions, closure (connectedComponentIn
        (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R) := by
      rw [T.decomposition.region_closure_cover]
      trivial
    obtain ⟨R, hR, hRz⟩ := mem_iUnion₂.mp hcover
    rw [T.refined.cover ⟨R, hR⟩] at hRz
    rcases hRz with (hc | hb) | hk
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hc
      have he : a.1 = (p, s) := by_contra (fun h => hz.1 a.1 h ha)
      have he' := congrArg (fun b : T.decomposition.vertices × (Bool × Bool) =>
        ((T.caps b.1).face b.2).carrier) he
      exact he' ▸ ha
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hb
      exact False.elim (hz.2 a.1 ha)
    · exact False.elim (hzcore ⟨R, hR⟩ hk)
  exact (((T.caps p).face s).boundary_image_subset_frontier 0
    ⟨t, Ioo_subset_Icc_self ht, rfl⟩).2 (mem_interior_iff_mem_nhds.mpr hint)


theorem open_cap_chord_mem_region_of_not_mem_bands
    (p : T.decomposition.vertices) (s : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier) :
    (((T.caps p).face s).boundary 0).map t ∈ connectedComponentIn
      (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ (T.region p s) := by
  obtain ⟨R, hR⟩ := T.exists_core_at_open_cap_chord p s ht hband
  have hreg := T.refined.in_region R hR
  have hcap := T.cap_regions p s
    (((T.caps p).open_chord_mem_carrier_iff s s ht).mpr rfl)
  have he : R = T.region p s := by
    by_contra hne
    exact disjoint_left.mp (T.decomposition.region_disjoint_closure hne) hreg hcap
  exact he ▸ hreg


theorem collar_germ_at_open_cap_chord
    (p : T.decomposition.vertices) (s : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier) :
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region (T.region p s) =ᶠ[𝓝 ((((T.caps p).face s).boundary 0).map t)]
        ((T.caps p).face s).carrier := by
  filter_upwards [T.cap_chord_avoidance_germ p s ht hband] with z hz
  apply propext
  constructor
  · rintro (hc | hb)
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hc
      have he : a.1 = (p, s) := by_contra (fun h => hz.1 a.1 h ha)
      exact congrArg (fun b : T.decomposition.vertices × (Bool × Bool) =>
        ((T.caps b.1).face b.2).carrier) he ▸ ha
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hb
      exact False.elim (hz.2 a.1 ha)
  · intro h
    exact Or.inl (mem_iUnion.mpr ⟨⟨(p, s), rfl⟩, h⟩)


theorem cap_core_union_mem_nhds
    (p : T.decomposition.vertices) (s : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier) :
    ((T.caps p).face s).carrier ∪
      ((chartAt Plane (T.chart (T.region p s) : S)).symm ''
        (T.refined.mesh (T.region p s)).toPlaneComplex.support) ∈
          𝓝 ((((T.caps p).face s).boundary 0).map t) := by
  let : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  have hU : IsOpen (connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
    T.decomposition.radius)ᶜ (T.region p s)) := (isClosed_chartDiskBoundaryUnion
      T.decomposition.centers T.decomposition.radius).isOpen_compl.connectedComponentIn
  filter_upwards [hU.mem_nhds (T.open_cap_chord_mem_region_of_not_mem_bands p s ht hband),
    T.collar_germ_at_open_cap_chord p s ht hband] with z hz hzc
  have hc := T.refined.cover (T.region p s) ▸ subset_closure hz
  rcases hc with h | h
  · exact Or.inl ((propext_iff.mp hzc).mp h)
  · exact Or.inr h


def capChordPoint (p : T.decomposition.vertices) (s : Bool × Bool) (t : ℝ) : Plane :=
  (1 - t) • (T.caps p).planarCoordinates s ((T.caps p).scale, 0) +
    t • (T.caps p).planarCoordinates s (0, (T.caps p).scale)

omit [T2Space S] in
theorem capChordPoint_mem_target (p : T.decomposition.vertices) (s : Bool × Bool)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    T.capChordPoint p s t ∈ (chartAt Plane (T.chart (T.region p s) : S)).target := by
  rw [capChordPoint, ← (T.caps p).planar_chord]
  apply (T.caps p).planar_target s
  apply ((T.caps p).planarCoordinates s).map_source
  exact (T.caps p).planar_source s
    ⟨mul_nonneg (sub_nonneg.mpr ht.2) (T.caps p).scale_pos.le,
      mul_nonneg ht.1 (T.caps p).scale_pos.le, by nlinarith⟩

omit [T2Space S] in
theorem capChordPoint_map (p : T.decomposition.vertices) (s : Bool × Bool) (t : ℝ) :
    (chartAt Plane (T.chart (T.region p s) : S)).symm (T.capChordPoint p s t) =
      (((T.caps p).face s).boundary 0).map t := by
  rw [capChordPoint, (T.caps p).planar_first s _ ⟨(T.caps p).scale_pos.le, le_rfl⟩,
    (T.caps p).planar_second s _ ⟨(T.caps p).scale_pos.le, le_rfl⟩]
  exact ((T.caps p).chord_map s t).symm




theorem exists_collar_halfspace_at_open_cap_chord
    (p : T.decomposition.vertices) (s : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier) :
    ∃ l : Plane →ᵃ[ℝ] ℝ, Function.Surjective l ∧
      (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs T.chains
        T.bands T.caps T.region (T.region p s), ∃ a : ℝ, a ≠ 0 ∧ l = a • k) ∧
      l (T.capChordPoint p s t) = 0 ∧
      (chartAt Plane (T.chart (T.region p s) : S)).symm ⁻¹'
        T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
          T.caps T.region (T.region p s) =ᶠ[𝓝 (T.capChordPoint p s t)] {z | l z ≤ 0} := by
  let B := T.caps p
  let C := (chartAt Plane (T.chart (T.region p s) : S)).symm
  let f := B.chordSupportingLine s
  have hs := T.capChordPoint_mem_target p s (Ioo_subset_Icc_self ht)
  have hc : C ⁻¹' T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains
      T.bands T.caps T.region (T.region p s) =ᶠ[𝓝 (T.capChordPoint p s t)]
        C ⁻¹' (B.face s).carrier := by
    have hC : Tendsto C (𝓝 (T.capChordPoint p s t))
        (𝓝 ((((T.caps p).face s).boundary 0).map t)) := by
      simpa only [C, T.capChordPoint_map] using (C.continuousAt hs).tendsto
    exact (T.collar_germ_at_open_cap_chord p s ht hband).comp_tendsto hC
  have hi : C ⁻¹' (B.face s).carrier =ᶠ[𝓝 (T.capChordPoint p s t)]
      C.symm '' (B.face s).carrier := by
    filter_upwards [C.open_source.mem_nhds hs] with z hz
    apply propext
    constructor
    · intro h
      exact ⟨C z, h, C.left_inv hz⟩
    · rintro ⟨y, hy, rfl⟩
      have hys := T.chart_source (T.region p s) (T.cap_regions p s hy)
      change C (C.symm y) ∈ (B.face s).carrier
      simpa only [C.right_inv hys] using hy
  have hfmem : f ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region (T.region p s) := by
    apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
    exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region rfl
  obtain ⟨hz, b, hb⟩ := B.chart_carrier_chord_supportingLine_germ s ht
  change f (T.capChordPoint p s t) = 0 at hz
  have hh := hc.trans hi
  cases b
  · refine ⟨f, (B.chordSupportingLine_spec s).1, ⟨f, hfmem, 1, one_ne_zero, ?_⟩, hz, ?_⟩
    · simp
    · filter_upwards [hh, hb] with z hhz hbz
      apply propext
      apply (propext_iff.mp hhz).trans
      change z ∈ chartAt Plane (T.chart (T.region p s) : S) '' (B.face s).carrier ↔ f z ≤ 0
      simpa only [Bool.false_eq_true, ite_false, neg_nonneg] using hbz
  · refine ⟨-f, ?_, ⟨f, hfmem, -1, neg_ne_zero.mpr one_ne_zero, ?_⟩, ?_, ?_⟩
    · intro r
      obtain ⟨z, hz⟩ := (B.chordSupportingLine_spec s).1 (-r)
      exact ⟨z, by simpa using congrArg Neg.neg hz⟩
    · simp
    · change -f (T.capChordPoint p s t) = 0
      rw [hz, neg_zero]
    · filter_upwards [hh, hb] with z hhz hbz
      apply propext
      apply (propext_iff.mp hhz).trans
      change z ∈ chartAt Plane (T.chart (T.region p s) : S) '' (B.face s).carrier ↔ -f z ≤ 0
      simpa only [ite_true, neg_nonpos] using hbz



theorem exists_core_halfspace_at_open_cap_chord
    (p : T.decomposition.vertices) (s : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier) :
    ∃ l : Plane →ᵃ[ℝ] ℝ, Function.Surjective l ∧
      (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs T.chains
        T.bands T.caps T.region (T.region p s), ∃ a : ℝ, a ≠ 0 ∧ l = a • k) ∧
      l (T.capChordPoint p s t) = 0 ∧
      (T.refined.mesh (T.region p s)).toPlaneComplex.support =ᶠ[𝓝 (T.capChordPoint p s t)]
        {z | 0 ≤ l z} := by
  obtain ⟨l, hl, hlines, hz, hlocal⟩ :=
    T.exists_collar_halfspace_at_open_cap_chord p s ht hband
  refine ⟨l, hl, hlines, hz, ?_⟩
  have hc := T.core_complement_germ_of_mem_region (T.region p s) (T.capChordPoint p s t)
    (T.capChordPoint_mem_target p s (Ioo_subset_Icc_self ht)) (by
      rw [T.capChordPoint_map]
      exact T.open_cap_chord_mem_region_of_not_mem_bands p s ht hband)
  have hi := support_eventuallyEq_interior hlocal
  rw [interior_affine_halfspace_nonpos l hl] at hi
  filter_upwards [hc, hi] with z hcz hiz
  apply propext
  have he := propext_iff.mp hcz
  change _ ↔ ¬ interior _ z at he
  rw [hiz] at he
  exact he.trans not_lt

set_option maxHeartbeats 800000 in


theorem vertex_contribution_eq_cap_add_core
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (s : Bool × Bool)
    {q : S} (hq : q ∈ interior (((T.caps p).face s).carrier ∪
      (chartAt Plane (T.chart (T.region p s) : S)).symm ''
        (T.refined.mesh (T.region p s)).toPlaneComplex.support)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      meshVertexAngleContribution g ((T.caps p).coordinates s)
        (T.refinement.mesh (.inl (p, s))) q +
      ∑ u : (T.refined.mesh (T.region p s)).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart (T.region p s) : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨T.region p s, u⟩))) q := by
  rw [T.vertex_contribution_eq_parent_sum]
  have h := mesh_family_contribution_eq_two_subfamily_sums g T.refinement.mesh
    T.parentCoordinates T.refinement.face (T.refinement.mesh_source T.parent_source)
    T.refinement.carrier_eq T.refinement.intersection_frontier
    (fun _ : Unit => (.inl (p, s) : T.Parent))
    (fun u : (T.refined.mesh (T.region p s)).Triangle =>
      (.inr (.inr ⟨T.region p s, u⟩) : T.Parent))
    (fun _ _ _ => Subsingleton.elim _ _) (by intro a b h; simpa using h)
    (by intro a b h; cases h) (q := q) ?_
  · simp only [Fintype.sum_unique] at h
    change (∑ i, meshVertexAngleContribution g (T.parentCoordinates i)
      (T.refinement.mesh i) q) =
      meshVertexAngleContribution g ((T.caps p).coordinates s)
        (T.refinement.mesh (.inl (p, s))) q +
      ∑ u : (T.refined.mesh (T.region p s)).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart (T.region p s) : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨T.region p s, u⟩))) q at h
    exact h
  · rw [T.core_parent_support_union]
    rw [iUnion_const, (T.refinement.subdivision (.inl (p, s))).support]
    change q ∈ interior (((T.caps p).coordinates s ''
      convexHull ℝ (range (rightTriangleBasis (T.caps p).scale_pos))) ∪ _)
    rwa [← (T.caps p).carrier_eq s]



theorem cap_contribution_at_open_chord_canonical_vertex
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (s : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : (((T.caps p).face s).boundary 0).map t = q.1) :
    meshVertexAngleContribution g ((T.caps p).coordinates s)
      (T.refinement.mesh (.inl (p, s))) q.1 = Real.pi := by
  have hused := T.parent_mesh_vertex_is_used q (.inl (p, s)) (by
    rw [(T.refinement.subdivision (.inl (p, s))).support]
    change q.1 ∈ (T.caps p).coordinates s ''
      convexHull ℝ (range (rightTriangleBasis (T.caps p).scale_pos))
    rw [← (T.caps p).carrier_eq, ← hq]
    exact ((T.caps p).open_chord_mem_carrier_iff s s ht).mpr rfl)
  have heq : T.refinement.mesh (.inl (p, s)) =
      (TriangleMesh.single (rightTriangleBasis (T.caps p).scale_pos)
        (rightTriangleBasis (T.caps p).scale_pos).ind).refineByLines
          (T.refinement.subdivision (.inl (p, s))).refinement_lines :=
    (T.refinement.subdivision (.inl (p, s))).mesh_eq_refineByLines
  rw [heq] at hused
  have hfan := (T.caps p).open_boundary_refined_vertex_fan g s 0
    (T.refinement.subdivision (.inl (p, s))).refinement_lines ht (by
      obtain ⟨u, v, hv, he⟩ := hused
      exact ⟨u, v, hv, he.trans hq.symm⟩)
  simpa only [← heq, hq] using hfan



theorem core_contribution_at_open_cap_chord_canonical_vertex
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (s : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : (((T.caps p).face s).boundary 0).map t = q.1) :
    (∑ u : (T.refined.mesh (T.region p s)).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart (T.region p s) : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨T.region p s, u⟩))) q.1) = Real.pi := by
  obtain ⟨l, hl, hlines, hz, hlocal⟩ :=
    T.exists_core_halfspace_at_open_cap_chord p s ht hband
  have hmem : T.capChordPoint p s t ∈ (T.refined.mesh (T.region p s)).toPlaneComplex.support := by
    apply (propext_iff.mp hlocal.eq_of_nhds).mpr
    change 0 ≤ l (T.capChordPoint p s t)
    rw [hz]
  exact T.core_contribution_at_straight_canonical_vertex g (T.region p s) q
    ((T.capChordPoint_map p s t).trans hq) hmem l hl hlines hz hlocal



theorem canonical_vertex_fan_on_open_cap_chord_of_not_mem_bands
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (s : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (((T.caps p).face s).boundary 0).map t ∉ (T.bands a.1 a.2).faces.carrier)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : (((T.caps p).face s).boundary 0).map t = q.1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  have hint := mem_interior_iff_mem_nhds.mpr (T.cap_core_union_mem_nhds p s ht hband)
  rw [hq] at hint
  rw [T.vertex_contribution_eq_cap_add_core g p s hint,
    T.cap_contribution_at_open_chord_canonical_vertex g p s ht q hq,
    T.core_contribution_at_open_cap_chord_canonical_vertex g p s ht hband q hq]
  ring

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
