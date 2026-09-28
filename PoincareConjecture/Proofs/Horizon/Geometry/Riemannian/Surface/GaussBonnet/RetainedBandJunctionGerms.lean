import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAttachmentGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedTopCornerFans

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

omit [T2Space S] in

theorem band_pair_unique_at_shared_cut
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) {q : S}
    (hq : q ∈ (T.bands p i).faces.rightCut)
    (a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs)
    (hR : a.1.1.1 = p.1.1) (ha : q ∈ (T.bands a.1 a.2).faces.carrier) :
    a = ⟨p, i⟩ ∨ a = ⟨p, j⟩ := by
  have hqi := (T.bands p i).faces.rightCut_subset_carrier hq
  have hl : q ∉ (T.bands p i).faces.leftCut := fun h =>
    (disjoint_left.mp (T.bands p i).faces.leftCut_disjoint_rightCut) h hq
  by_cases he : a.1.1.2 = p.1.2
  · have hp : a.1 = p := Subtype.ext (Prod.ext hR he)
    rcases a with ⟨p', k⟩
    dsimp at hp
    subst p'
    by_cases hki : k = i
    · exact Or.inl (by subst k; rfl)
    by_cases hnext : i.succ = k.castSucc
    · have hkj : k = j := Fin.ext (congrArg (fun x : Fin ((T.graphs p).count + 1) => x.val)
        (hnext.symm.trans hij))
      exact Or.inr (by subst k; rfl)
    by_cases hprev : k.succ = i.castSucc
    · have hcut := T.band_adjacent p k i hprev
      have hleft := (T.bands p i).leftCut_eq_segment ((T.graphs p).cut_lt i).le
      simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply, ← hprev] at hleft
      exact False.elim (hl (hleft.symm ▸ hcut ▸ (show q ∈
        (T.bands p k).faces.carrier ∩ (T.bands p i).faces.carrier from ⟨ha, hqi⟩)))
    have hgap : i.val + 1 < k.val ∨ k.val + 1 < i.val := by
      have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      have hn : i.val + 1 ≠ k.val := fun h => hnext (Fin.ext h)
      have hp : k.val + 1 ≠ i.val := fun h => hprev (Fin.ext h)
      omega
    exact False.elim ((disjoint_left.mp (T.bands_disjoint_of_separated
      ⟨p, i⟩ ⟨p, k⟩ (Or.inr ⟨rfl, hgap⟩))) hqi ha)
  · exact False.elim ((disjoint_left.mp (T.bands_disjoint_of_separated
      a ⟨p, i⟩ (Or.inl he))) ha hqi)

omit [T2Space S] in

theorem not_mem_region_caps_at_shared_cut
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) {q : S}
    (hq : q ∈ (T.bands p i).faces.rightCut) :
    q ∉ T.decomposition.vertexCapsInRegion T.caps T.region p.1.1 := by
  have hlast : i ≠ (T.graphs p).lastPiece := by
    intro h
    have hv := congrArg Fin.val hij
    rw [h, (T.graphs p).lastPiece_succ] at hv
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  intro hc
  have h := T.band_caps p i ▸ (show q ∈ (T.bands p i).faces.carrier ∩
    T.decomposition.vertexCapsInRegion T.caps T.region p.1.1 from
      ⟨(T.bands p i).faces.rightCut_subset_carrier hq, hc⟩)
  rcases h with h | h
  · split_ifs at h with hi
    · subst i
      exact (disjoint_left.mp (T.bands p (T.graphs p).firstPiece).faces.leftCut_disjoint_rightCut)
        (T.first_band_leftCut_eq_chordSegment p ▸ h) hq
    · exact h
  · simp only [if_neg hlast, mem_empty_iff_false] at h

theorem collar_germ_at_shared_band_cut
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) {q : S}
    (hq : q ∈ (T.bands p i).faces.rightCut) :
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region p.1.1 =ᶠ[𝓝 q]
        ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier : Set S) := by
  let I := {a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs //
    a.1.1.1 = p.1.1}
  have hb : ∀ᶠ z in 𝓝 q, ∀ a : I, a.1 ≠ ⟨p, i⟩ → a.1 ≠ ⟨p, j⟩ →
      z ∉ (T.bands a.1.1 a.1.2).faces.carrier := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases hi : a.1 = ⟨p, i⟩
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hi))
    by_cases hj : a.1 = ⟨p, j⟩
    · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h hj))
    have hn : q ∉ (T.bands a.1.1 a.1.2).faces.carrier := by
      intro h
      exact (T.band_pair_unique_at_shared_cut p i j hij hq a.1 a.2 h).elim hi hj
    filter_upwards [(T.bands a.1.1 a.1.2).faces.isClosed_carrier.isOpen_compl.mem_nhds hn]
      with z hz
    exact fun _ _ => hz
  have hc := (T.decomposition.isCompact_vertexCapsInRegion T.caps T.region p.1.1).isClosed.isOpen_compl.mem_nhds
    (T.not_mem_region_caps_at_shared_cut p i j hij hq)
  filter_upwards [hb, hc] with z hz hzc
  apply propext
  change (z ∈ T.decomposition.vertexCapsInRegion T.caps T.region p.1.1 ∪
    T.decomposition.graphBandsInRegion T.chart T.cut T.graphs T.chains T.bands p.1.1) ↔ _
  rw [mem_union, or_iff_right hzc]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_iUnion.mp h
    by_cases hi : a.1 = ⟨p, i⟩
    · exact Or.inl (congrArg (fun b :
        T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs =>
          (T.bands b.1 b.2).faces.carrier) hi ▸ ha)
    have hj : a.1 = ⟨p, j⟩ := by_contra (fun hn => hz a hi hn ha)
    exact Or.inr (congrArg (fun b :
      T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs =>
        (T.bands b.1 b.2).faces.carrier) hj ▸ ha)
  · rintro (h | h)
    · exact mem_iUnion.mpr ⟨⟨⟨p, i⟩, rfl⟩, h⟩
    · exact mem_iUnion.mpr ⟨⟨⟨p, j⟩, rfl⟩, h⟩

def bandJunctionPoint (p : T.decomposition.IncidentEdgeIndex)
    (k : Fin ((T.graphs p).count + 1)) : Plane :=
  chartAt Plane (T.chart p.1.1 : S)
    ((T.decomposition.edge p.1.2.1 p.1.2.2).map ((T.graphs p).cut k)) +
      T.length • (T.chains p).direction k

omit [T2Space S] in
theorem bandJunctionPoint_eq_last_top
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) :
    T.bandJunctionPoint p i.succ =
      (T.bands p i).chartTopVertex (Fin.last (T.bands p i).faces.interface.count) := by
  let B := T.bands p i
  apply ((T.graphs p).piece i).frame.injective
  apply collarParameterEquiv.symm.injective
  have h := B.ambient_last_vertex ((T.graphs p).cut_lt i).le
  simpa only [bandJunctionPoint, Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm,
    FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces.chartTopVertex,
    ContinuousLinearEquiv.apply_symm_apply, ObliqueBandFaces.planarTopVertex] using h

omit [T2Space S] in
theorem bandJunctionPoint_eq_first_top
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) :
    T.bandJunctionPoint p i.castSucc = (T.bands p i).chartTopVertex 0 := by
  let B := T.bands p i
  apply ((T.graphs p).piece i).frame.injective
  apply collarParameterEquiv.symm.injective
  have h := B.ambient_first_vertex ((T.graphs p).cut_lt i).le
  simpa only [bandJunctionPoint, Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm,
    FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces.chartTopVertex,
    ContinuousLinearEquiv.apply_symm_apply, ObliqueBandFaces.planarTopVertex] using h

omit [T2Space S] in
theorem ambientTopPoint_one_eq_bandJunctionPoint
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) :
    (T.bands p i).ambientTopPoint 1 = T.bandJunctionPoint p i.succ := by
  let B := T.bands p i
  have hlast : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
    apply Fin.ext
    dsimp [ObliqueBandFaces.lastCell]
    have hn := B.faces.interface.count_pos
    omega
  have h := T.band_internal_top_point_eq_vertex p i B.faces.lastCell
  rw [hlast, B.faces.cut_last] at h
  exact h.trans (T.bandJunctionPoint_eq_last_top p i).symm

omit [T2Space S] in
theorem bandJunctionPoint_mem_source
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) :
    T.bandJunctionPoint p i.succ ∈ (chartAt Plane (T.chart p.1.1 : S)).target := by
  rw [← T.ambientTopPoint_one_eq_bandJunctionPoint]
  exact (T.bands p i).ambientTopPoint_mem_source (by simp)

omit [T2Space S] in
theorem bandJunctionPoint_mem_rightCut
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) :
    (chartAt Plane (T.chart p.1.1 : S)).symm (T.bandJunctionPoint p i.succ) ∈
      (T.bands p i).faces.rightCut := by
  rw [(T.chains p).rightCut_eq_cutRay (T.bands p) i]
  exact ⟨T.length, ⟨T.length_pos.le, le_rfl⟩, rfl⟩

omit [T2Space S] in

theorem bandJunctionPoint_mem_region
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count) :
    (chartAt Plane (T.chart p.1.1 : S)).symm (T.bandJunctionPoint p i.succ) ∈
      connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
        T.decomposition.radius)ᶜ p.1.1 := by
  rw [← T.ambientTopPoint_one_eq_bandJunctionPoint, (T.bands p i).ambientTopPoint_map]
  exact T.band_positive_height_mem_region p i (by simp)
    ((T.bands p i).faces.height_pos (by simp)) le_rfl

theorem coordinate_collar_germ_at_band_junction
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) :
    (chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
        T.caps T.region p.1.1 =ᶠ[𝓝 (T.bandJunctionPoint p i.succ)]
      (chartAt Plane (T.chart p.1.1 : S)) ''
        ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier) := by
  let C := (chartAt Plane (T.chart p.1.1 : S)).symm
  have hs := T.bandJunctionPoint_mem_source p i
  have h := (T.collar_germ_at_shared_band_cut p i j hij
    (T.bandJunctionPoint_mem_rightCut p i)).comp_tendsto (C.continuousAt hs)
  apply h.trans
  filter_upwards [C.open_source.mem_nhds hs] with z hz
  apply propext
  change C z ∈ ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier) ↔
    z ∈ C.symm '' ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier)
  constructor
  · intro h
    exact ⟨C z, h, C.left_inv hz⟩
  · rintro ⟨y, hy, rfl⟩
    have hys : y ∈ C.target := T.chart_source p.1.1 (hy.elim
      (fun h => T.band_regions p i h) (fun h => T.band_regions p j h))
    simpa only [C.right_inv hys] using hy

theorem core_complement_germ_at_band_junction
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) :
    (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (T.bandJunctionPoint p i.succ)]
      (interior ((chartAt Plane (T.chart p.1.1 : S)) ''
        ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier)))ᶜ := by
  have hc := T.core_complement_germ_of_mem_region p.1.1 _
    (T.bandJunctionPoint_mem_source p i) (T.bandJunctionPoint_mem_region p i)
  have hi := support_eventuallyEq_interior (T.coordinate_collar_germ_at_band_junction p i j hij)
  filter_upwards [hc, hi] with z hcz hiz
  change (T.refined.mesh p.1.1).toPlaneComplex.support z = ¬interior _ z
  change (T.refined.mesh p.1.1).toPlaneComplex.support z = ¬interior _ z at hcz
  rwa [hiz] at hcz

theorem band_pair_core_union_mem_nhds_at_junction
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) :
    ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier) ∪
      ((chartAt Plane (T.chart p.1.1 : S)).symm ''
        (T.refined.mesh p.1.1).toPlaneComplex.support) ∈
      𝓝 ((chartAt Plane (T.chart p.1.1 : S)).symm (T.bandJunctionPoint p i.succ)) := by
  let : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  have hU : IsOpen (connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
    T.decomposition.radius)ᶜ p.1.1) := (isClosed_chartDiskBoundaryUnion T.decomposition.centers
      T.decomposition.radius).isOpen_compl.connectedComponentIn
  have hc := T.collar_germ_at_shared_band_cut p i j hij (T.bandJunctionPoint_mem_rightCut p i)
  filter_upwards [hU.mem_nhds (T.bandJunctionPoint_mem_region p i), hc] with y hy hcy
  have hcover := T.refined.cover p.1.1 ▸ subset_closure hy
  rcases hcover with h | h
  · exact Or.inl (propext_iff.mp hcy |>.mp h)
  · exact Or.inr h

set_option maxHeartbeats 1200000 in

theorem vertex_contribution_eq_band_pair_add_core_at_junction
    (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) :
    let q := (chartAt Plane (T.chart p.1.1 : S)).symm (T.bandJunctionPoint p i.succ)
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      ((∑ a : Fin (T.bands p i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates a)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))) q) +
       ∑ a : Fin (T.bands p j).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p j).faces.faceCoordinates a)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, j⟩, a⟩))) q) +
      ∑ u : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨p.1.1, u⟩))) q := by
  dsimp only
  let A := (Fin (T.bands p i).faces.interface.count × Bool) ⊕
    (Fin (T.bands p j).faces.interface.count × Bool)
  let left : A → T.Parent := Sum.elim
    (fun a => .inr (.inl ⟨⟨p, i⟩, a⟩)) (fun a => .inr (.inl ⟨⟨p, j⟩, a⟩))
  let right : (T.refined.mesh p.1.1).Triangle → T.Parent :=
    fun u => .inr (.inr ⟨p.1.1, u⟩)
  have hne : i ≠ j := by
    intro h
    have hv := congrArg Fin.val hij
    simp only [h, Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hl : Function.Injective left := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        simpa only [left, Sum.elim_inl, Sum.inr.injEq, Sum.inl.injEq,
          Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
      | inr b =>
        have hk : i = j := by
          have he := congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj h))
          have hv := congrArg (fun x : T.decomposition.IncidentGraphPieceIndex
            T.chart T.cut T.graphs => x.2.val) he
          exact Fin.ext hv
        exact False.elim (hne hk)
    | inr a =>
      cases b with
      | inl b =>
        have hk : j = i := by
          have he := congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj h))
          have hv := congrArg (fun x : T.decomposition.IncidentGraphPieceIndex
            T.chart T.cut T.graphs => x.2.val) he
          exact Fin.ext hv
        exact False.elim (hne hk.symm)
      | inr b =>
        apply congrArg Sum.inr
        simpa only [left, Sum.elim_inr, Sum.inr.injEq, Sum.inl.injEq,
          Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  have hr : Function.Injective right := by
    intro a b h
    simpa only [right, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  have hdis : ∀ a b, left a ≠ right b := by
    intro a b h
    cases a <;> cases h
  have hleft : (⋃ a : A, T.parentCoordinates (left a) ''
      (T.refinement.mesh (left a)).toPlaneComplex.support) =
        (T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier := by
    rw [iUnion_sum]
    exact congrArg₂ (fun x y : Set S => x ∪ y)
      (T.band_parent_support_union p i) (T.band_parent_support_union p j)
  have hq := mem_interior_iff_mem_nhds.mpr
    (T.band_pair_core_union_mem_nhds_at_junction p i j hij)
  have he := mesh_family_contribution_eq_two_subfamily_sums g T.refinement.mesh T.parentCoordinates
    T.refinement.face (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
    T.refinement.intersection_frontier left right hl hr hdis
    (by rwa [hleft, T.core_parent_support_union p.1.1])
  rw [T.vertex_contribution_eq_parent_sum]
  dsimp only [A] at he
  simpa only [Fintype.sum_sum_type, left, right, Sum.elim_inl, Sum.elim_inr,
    parentCoordinates, FiniteChartRegionDecomposition.fittedFaceCoordinates] using he

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
