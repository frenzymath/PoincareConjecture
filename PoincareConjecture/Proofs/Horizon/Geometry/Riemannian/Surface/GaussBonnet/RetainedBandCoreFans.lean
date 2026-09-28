import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCollarGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCoreSectors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandInteriorFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedInteriorFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.AmbientTopEdges
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.UpperArcFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshSubfamilyContribution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem band_core_union_mem_nhds
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {t z : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : 0 < z) (hzh : z ≤ (T.bands p i).faces.height t) :
    (T.bands p i).faces.carrier ∪ ((chartAt Plane (T.chart p.1.1 : S)).symm ''
      (T.refined.mesh p.1.1).toPlaneComplex.support) ∈
      𝓝 (((T.graphs p).piece i).strip ((T.chains p).graphCuts i) (t, z)) := by
  let : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  have hU : IsOpen (connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
    T.decomposition.radius)ᶜ p.1.1) := (isClosed_chartDiskBoundaryUnion T.decomposition.centers
      T.decomposition.radius).isOpen_compl.connectedComponentIn
  have hqU := T.band_positive_height_mem_region p i ⟨ht.1.le, ht.2.le⟩ hz hzh
  have hc := T.collar_germ_at_interior_strip_point p i ht ⟨hz.le, hzh⟩
  filter_upwards [hU.mem_nhds hqU, hc] with y hy hcy
  have hcover := T.refined.cover p.1.1 ▸ subset_closure hy
  rcases hcover with h | h
  · exact Or.inl (propext_iff.mp hcy |>.mp h)
  · exact Or.inr h

set_option maxHeartbeats 800000 in

theorem vertex_contribution_eq_band_add_core
    (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {q : S} (hq : q ∈ interior ((T.bands p i).faces.carrier ∪
      (chartAt Plane (T.chart p.1.1 : S)).symm ''
        (T.refined.mesh p.1.1).toPlaneComplex.support)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      (∑ a : Fin (T.bands p i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates a)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))) q) +
      ∑ u : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨p.1.1, u⟩))) q := by
  rw [T.vertex_contribution_eq_parent_sum]
  apply mesh_family_contribution_eq_two_subfamily_sums g T.refinement.mesh T.parentCoordinates
    T.refinement.face (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
    T.refinement.intersection_frontier
    (fun a : Fin (T.bands p i).faces.interface.count × Bool => (.inr (.inl ⟨⟨p, i⟩, a⟩) : T.Parent))
    (fun u : (T.refined.mesh p.1.1).Triangle => (.inr (.inr ⟨p.1.1, u⟩) : T.Parent))
  · intro a b h
    simpa using h
  · intro a b h
    simpa using h
  · intro a b h
    cases h
  · rwa [T.band_parent_support_union p i, T.core_parent_support_union p.1.1]

theorem collar_halfspace_at_open_band_top
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j : Fin (T.bands p i).faces.interface.count) {t : ℝ}
    (ht : t ∈ Ioo ((T.bands p i).faces.cut j.castSucc) ((T.bands p i).faces.cut j.succ)) :
    (chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
        T.caps T.region p.1.1 =ᶠ[𝓝 ((T.bands p i).ambientTopPoint t)]
      {z | (T.bands p i).ambientTopFunctional j z ≤ 0} := by
  let B := T.bands p i
  let C := (chartAt Plane (T.chart p.1.1 : S)).symm
  have hcut (k : Fin (B.faces.interface.count + 1)) : B.faces.cut k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [B.faces.cut_first] using B.faces.cut_strictMono.monotone (Fin.zero_le k)
    · simpa only [B.faces.cut_last] using B.faces.cut_strictMono.monotone (Fin.le_last k)
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨((hcut j.castSucc).1.trans_lt ht.1), ht.2.trans_le (hcut j.succ).2⟩
  have hts : t ∈ Icc (0 : ℝ) 1 := ⟨hti.1.le, hti.2.le⟩
  have hs := B.ambientTopPoint_mem_source hts
  have hn := T.strip_point_not_mem_endpoint_cuts p i hti ⟨(B.faces.height_pos hts).le, le_rfl⟩
  have hb : C (B.ambientTopPoint t) ∈ B.faces.carrier := by
    rw [B.ambientTopPoint_map, B.carrier_eq_fixed_strip]
    exact mem_image_of_mem _ ⟨hts, (B.faces.height_pos hts).le, le_rfl⟩
  have hlocal := T.coordinate_collar_germ_of_band_away_from_endpoint_cuts p i hs hb
    (by simpa only [B.ambientTopPoint_map] using hn.1)
    (by simpa only [B.ambientTopPoint_map] using hn.2)
  have himage : C ⁻¹' B.faces.carrier =ᶠ[𝓝 (B.ambientTopPoint t)] C.symm '' B.faces.carrier := by
    filter_upwards [C.open_source.mem_nhds hs] with z hz
    apply propext
    change C z ∈ B.faces.carrier ↔ z ∈ C.symm '' B.faces.carrier
    constructor
    · intro h
      exact ⟨C z, h, C.left_inv hz⟩
    · rintro ⟨y, hy, rfl⟩
      have hys := T.chart_source p.1.1 (T.band_regions p i hy)
      simpa only [C.right_inv hys] using hy
  exact hlocal.trans (himage.trans (B.ambient_carrier_open_top_halfspace j ht))

theorem core_halfspace_at_open_band_top
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j : Fin (T.bands p i).faces.interface.count) {t : ℝ}
    (ht : t ∈ Ioo ((T.bands p i).faces.cut j.castSucc) ((T.bands p i).faces.cut j.succ)) :
    (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 ((T.bands p i).ambientTopPoint t)]
      {z | 0 ≤ (T.bands p i).ambientTopFunctional j z} := by
  let B := T.bands p i
  have hcut (k : Fin (B.faces.interface.count + 1)) : B.faces.cut k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [B.faces.cut_first] using B.faces.cut_strictMono.monotone (Fin.zero_le k)
    · simpa only [B.faces.cut_last] using B.faces.cut_strictMono.monotone (Fin.le_last k)
  have hts : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(hcut j.castSucc).1.trans ht.1.le, ht.2.le.trans (hcut j.succ).2⟩
  have hqU := T.band_positive_height_mem_region p i hts (B.faces.height_pos hts) le_rfl
  have hc := T.core_complement_germ_of_mem_region p.1.1 (B.ambientTopPoint t)
    (B.ambientTopPoint_mem_source hts) (by rwa [B.ambientTopPoint_map])
  have hi := support_eventuallyEq_interior (T.collar_halfspace_at_open_band_top p i j ht)
  rw [interior_affine_halfspace_nonpos _ (B.ambientTopFunctional_surjective j)] at hi
  filter_upwards [hc, hi] with z hcz hiz
  apply propext
  have he : z ∈ (T.refined.mesh p.1.1).toPlaneComplex.support ↔
      ¬ interior ((chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
        T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
          T.caps T.region p.1.1) z := propext_iff.mp hcz
  rw [hiz] at he
  exact he.trans not_lt

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
