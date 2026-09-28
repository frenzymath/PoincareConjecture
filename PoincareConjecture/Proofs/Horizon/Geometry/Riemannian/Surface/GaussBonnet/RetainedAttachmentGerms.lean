import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapBandSectorGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapEdgeFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCollarGerms







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

namespace ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph Plane S} {lo : ℝ → ℝ}
  {a b ua wa ub wb ra rb : ℝ} (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

omit [T2Space S] in


theorem leftCut_disjoint_rightCut : Disjoint B.leftCut B.rightCut := by
  rw [← B.left_height_image, ← B.right_height_image]
  apply disjoint_left.mpr
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have hxs : collarParameterEquiv.symm (0, x) ∈ B.coordinates.source :=
    B.band_subset_source (by simpa only [B.band_eq_subgraph, mem_ofPred_eq, mem_Icc,
      ContinuousLinearEquiv.apply_symm_apply] using
      (show (0 : ℝ) ∈ Icc 0 1 ∧ x ∈ Icc 0 (B.height 0) from ⟨by simp, hx⟩))
  have hys : collarParameterEquiv.symm (1, y) ∈ B.coordinates.source :=
    B.band_subset_source (by simpa only [B.band_eq_subgraph, mem_ofPred_eq, mem_Icc,
      ContinuousLinearEquiv.apply_symm_apply] using
      (show (1 : ℝ) ∈ Icc 0 1 ∧ y ∈ Icc 0 (B.height 1) from ⟨by simp, hy⟩))
  have h := congrArg (fun z => (collarParameterEquiv z).1)
    (B.coordinates.injOn hxs hys (hxq.trans hyq.symm))
  simp at h

omit [T2Space S] in
theorem leftCut_subset_carrier : B.leftCut ⊆ B.carrier := by
  rw [← B.left_height_image, B.carrier_eq_image]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, ?_, rfl⟩
  simpa only [B.band_eq_subgraph, mem_ofPred_eq, mem_Icc,
    ContinuousLinearEquiv.apply_symm_apply] using
    (show (0 : ℝ) ∈ Icc 0 1 ∧ x ∈ Icc 0 (B.height 0) from ⟨by simp, hx⟩)

omit [T2Space S] in
theorem rightCut_subset_carrier : B.rightCut ⊆ B.carrier := by
  rw [← B.right_height_image, B.carrier_eq_image]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, ?_, rfl⟩
  simpa only [B.band_eq_subgraph, mem_ofPred_eq, mem_Icc,
    ContinuousLinearEquiv.apply_symm_apply] using
    (show (1 : ℝ) ∈ Icc 0 1 ∧ x ∈ Icc 0 (B.height 1) from ⟨by simp, hx⟩)

end ObliqueBandFaces

namespace FiniteChartRegionDecomposition.CapGraphEndpoint

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {D : FiniteChartRegionDecomposition (M := S)}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : S)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → S}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions} {a b trim : ℝ} {terminal : Bool}
  {G : D.OrientedGraphPiece e R (chartAt Plane (chart R)).symm a b}
  (E : D.CapGraphEndpoint P region chart caps e R G terminal trim)

omit [T2Space S] in


theorem attachment_mem_chart_target {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    chartAt Plane (chart R) (D.edgeFromEndpoint e terminal trim) + r • E.direction ∈
      (chartAt Plane (chart R)).target := by
  rw [← E.chord_base, E.direction_eq]
  simpa only [E.sector_region] using
    (caps (D.edgeEndpoint e terminal)).chord_ray_mem_target E.sector
      (decide (E.radialEdge = 1)) hr

end FiniteChartRegionDecomposition.CapGraphEndpoint

namespace RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in


theorem band_unique_of_endpoint_incidence
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {q : S} (hq : q ∈ (T.bands p i).faces.carrier)
    (hl : i ≠ (T.graphs p).firstPiece → q ∉ (T.bands p i).faces.leftCut)
    (hr : i ≠ (T.graphs p).lastPiece → q ∉ (T.bands p i).faces.rightCut)
    (a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs)
    (hR : a.1.1.1 = p.1.1) (ha : q ∈ (T.bands a.1 a.2).faces.carrier) :
    a = ⟨p, i⟩ := by
  by_cases he : a.1.1.2 = p.1.2
  · have hp : a.1 = p := Subtype.ext (Prod.ext hR he)
    rcases a with ⟨p', j⟩
    dsimp at hp
    subst p'
    by_cases hji : j = i
    · subst j
      rfl
    by_cases hnext : i.succ = j.castSucc
    · have hi : i ≠ (T.graphs p).lastPiece := by
        intro hi
        have hv := congrArg Fin.val hnext
        rw [hi, (T.graphs p).lastPiece_succ] at hv
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      have hcut := T.band_adjacent p i j hnext
      have hright := (T.bands p i).rightCut_eq_segment ((T.graphs p).cut_lt i).le
      simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply] at hright
      exact False.elim (hr hi (hright.symm ▸ hcut ▸ (show q ∈
        (T.bands p i).faces.carrier ∩ (T.bands p j).faces.carrier from ⟨hq, ha⟩)))
    by_cases hprev : j.succ = i.castSucc
    · have hi : i ≠ (T.graphs p).firstPiece := by
        intro hi
        have hv := congrArg Fin.val hprev
        rw [hi, (T.graphs p).firstPiece_castSucc] at hv
        simp only [Fin.val_zero, Fin.val_succ] at hv
        omega
      have hcut := T.band_adjacent p j i hprev
      have hleft := (T.bands p i).leftCut_eq_segment ((T.graphs p).cut_lt i).le
      simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply, ← hprev] at hleft
      exact False.elim (hl hi (hleft.symm ▸ hcut ▸ (show q ∈
        (T.bands p j).faces.carrier ∩ (T.bands p i).faces.carrier from ⟨ha, hq⟩)))
    have hgap : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
      have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      have hn : i.val + 1 ≠ j.val := fun h => hnext (Fin.ext h)
      have hp : j.val + 1 ≠ i.val := fun h => hprev (Fin.ext h)
      omega
    exact False.elim ((Set.disjoint_left.mp (T.bands_disjoint_of_separated
      ⟨p, i⟩ ⟨p, j⟩ (Or.inr ⟨rfl, hgap⟩))) hq ha)
  · exact False.elim ((Set.disjoint_left.mp (T.bands_disjoint_of_separated
      a ⟨p, i⟩ (Or.inl he))) ha hq)



theorem cap_unique_at_open_chord (p : T.decomposition.vertices) (s : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (v : T.decomposition.vertices) (j : Bool × Bool)
    (hq : (((T.caps p).face s).boundary 0).map t ∈ ((T.caps v).face j).carrier) :
    v = p ∧ j = s := by
  have hp : (((T.caps p).face s).boundary 0).map t ∈ ((T.caps p).face s).carrier :=
    ((T.caps p).open_chord_mem_carrier_iff s s ht).mpr rfl
  have hv : v = p := by
    by_contra hne
    exact (disjoint_left.mp (T.caps_disjoint_of_vertices_ne v p hne j s)) hq hp
  subst v
  exact ⟨rfl, ((T.caps p).open_chord_mem_carrier_iff s j ht).mp hq⟩



theorem collar_germ_of_unique_cap_band
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (v : T.decomposition.vertices) (s : Bool × Bool) {q : S}
    (hregion : T.region v s = p.1.1)
    (hcap : ∀ w j, q ∈ ((T.caps w).face j).carrier → T.region w j = p.1.1 →
      w = v ∧ j = s)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      a.1.1.1 = p.1.1 → q ∈ (T.bands a.1 a.2).faces.carrier → a = ⟨p, i⟩) :
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region p.1.1 =ᶠ[𝓝 q]
        (((T.caps v).face s).carrier ∪ (T.bands p i).faces.carrier : Set S) := by
  obtain ⟨N, hN, hqN, heqN⟩ :=
    T.decomposition.exists_neighborhood_vertexCapsInRegion_eq_cap T.caps T.region hregion hcap
  let I := {a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs //
    a.1.1.1 = p.1.1}
  have hb : ∀ᶠ z in 𝓝 q, ∀ a : I, a.1 ≠ ⟨p, i⟩ →
      z ∉ (T.bands a.1.1 a.1.2).faces.carrier := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : a.1 = ⟨p, i⟩
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h ha))
    · have hn : q ∉ (T.bands a.1.1 a.1.2).faces.carrier := fun h => ha (hband a.1 a.2 h)
      filter_upwards [(T.bands a.1.1 a.1.2).faces.isClosed_carrier.isOpen_compl.mem_nhds hn]
        with z hz
      exact fun _ => hz
  filter_upwards [hN.mem_nhds hqN, hb] with z hzN hz
  apply propext
  have hc : z ∈ T.decomposition.vertexCapsInRegion T.caps T.region p.1.1 ↔
      z ∈ ((T.caps v).face s).carrier := by
    constructor
    · intro h
      exact (heqN ▸ (show z ∈ N ∩ T.decomposition.vertexCapsInRegion T.caps T.region p.1.1
        from ⟨hzN, h⟩)).2
    · intro h
      exact (heqN.symm ▸ (show z ∈ N ∩ ((T.caps v).face s).carrier from ⟨hzN, h⟩)).2
  have hb' : z ∈ T.decomposition.graphBandsInRegion T.chart T.cut T.graphs T.chains
      T.bands p.1.1 ↔ z ∈ (T.bands p i).faces.carrier := by
    constructor
    · intro h
      obtain ⟨a, ha⟩ := mem_iUnion.mp h
      have he : a.1 = ⟨p, i⟩ := by_contra (fun hn => hz a hn ha)
      have he' := congrArg (fun b : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs =>
        (T.bands b.1 b.2).faces.carrier) he
      exact he' ▸ ha
    · intro h
      exact mem_iUnion.mpr ⟨⟨⟨p, i⟩, rfl⟩, h⟩
  exact or_congr hc hb'



theorem collar_germ_at_first_upper_attachment
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let q := (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
          T.length • (T.leftCap p).direction)
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region p.1.1 =ᶠ[𝓝 q]
        (((T.caps (T.decomposition.edgeEndpoint p.1.2 false)).face (T.leftCap p).sector).carrier ∪
          (T.bands p (T.graphs p).firstPiece).faces.carrier : Set S) := by
  let q := (chartAt Plane (T.chart p.1.1 : S)).symm
    (chartAt Plane (T.chart p.1.1 : S)
      (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
        T.length • (T.leftCap p).direction)
  have hl : q ∈ (T.bands p (T.graphs p).firstPiece).faces.leftCut := by
    rw [T.first_band_leftCut_eq_chordSegment p]
    exact ⟨T.length, ⟨T.length_pos.le, le_rfl⟩, rfl⟩
  apply T.collar_germ_of_unique_cap_band p (T.graphs p).firstPiece
    (T.decomposition.edgeEndpoint p.1.2 false) (T.leftCap p).sector
    (T.leftCap p).sector_region
  · intro w j hq _
    rw [(T.leftCap p).chord_map] at hq
    apply T.cap_unique_at_open_chord _ _ (v := w) (j := j) _ hq
    split_ifs <;> constructor <;> linarith [T.length_pos]
  · intro a hR ha
    apply T.band_unique_of_endpoint_incidence p (T.graphs p).firstPiece
      ((T.bands p (T.graphs p).firstPiece).faces.leftCut_subset_carrier hl)
      (fun h => (h rfl).elim) _ a hR ha
    intro _ hright
    exact (disjoint_left.mp (T.bands p (T.graphs p).firstPiece).faces.leftCut_disjoint_rightCut)
      hl hright



theorem collar_germ_at_last_upper_attachment
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let q := (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
          T.length • (T.rightCap p).direction)
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region p.1.1 =ᶠ[𝓝 q]
        (((T.caps (T.decomposition.edgeEndpoint p.1.2 true)).face (T.rightCap p).sector).carrier ∪
          (T.bands p (T.graphs p).lastPiece).faces.carrier : Set S) := by
  let q := (chartAt Plane (T.chart p.1.1 : S)).symm
    (chartAt Plane (T.chart p.1.1 : S)
      (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
        T.length • (T.rightCap p).direction)
  have hr' : q ∈ (T.bands p (T.graphs p).lastPiece).faces.rightCut := by
    rw [T.last_band_rightCut_eq_chordSegment p]
    exact ⟨T.length, ⟨T.length_pos.le, le_rfl⟩, rfl⟩
  apply T.collar_germ_of_unique_cap_band p (T.graphs p).lastPiece
    (T.decomposition.edgeEndpoint p.1.2 true) (T.rightCap p).sector
    (T.rightCap p).sector_region
  · intro w j hq _
    rw [(T.rightCap p).chord_map] at hq
    apply T.cap_unique_at_open_chord _ _ (v := w) (j := j) _ hq
    split_ifs <;> constructor <;> linarith [T.length_pos]
  · intro a hR ha
    apply T.band_unique_of_endpoint_incidence p (T.graphs p).lastPiece
      ((T.bands p (T.graphs p).lastPiece).faces.rightCut_subset_carrier hr')
      _ (fun h => (h rfl).elim) a hR ha
    intro _ hleft
    exact (disjoint_left.mp (T.bands p (T.graphs p).lastPiece).faces.leftCut_disjoint_rightCut)
      hleft hr'

omit [T2Space S] in
private theorem cap_carrier_subset_region_chart_source
    (v : T.decomposition.vertices) (s : Bool × Bool) :
    ((T.caps v).face s).carrier ⊆ (chartAt Plane (T.chart (T.region v s) : S)).source := by
  rw [(T.caps v).carrier_eq s]
  rintro _ ⟨z, hz, rfl⟩
  exact (T.caps v).coordinates_target s
    (((T.caps v).coordinates s).map_source ((T.caps v).triangle_subset_source s hz))

omit [T2Space S] [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S] in
private theorem preimage_membership_iff_image
    (F : OpenPartialHomeomorph S Plane) {K : Set S} (hK : K ⊆ F.source)
    {z : Plane} (hz : z ∈ F.target) :
    F.symm z ∈ K ↔ z ∈ F '' K := by
  constructor
  · intro h
    exact ⟨F.symm z, h, F.right_inv hz⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [F.left_inv (hK hx)]



theorem coordinate_collar_first_upper_attachment_reflex_germ
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let B := T.bands p (T.graphs p).firstPiece
    ∀ᶠ z in 𝓝 (chartAt Plane (T.chart p.1.1 : S)
      (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
        T.length • (T.leftCap p).direction),
      (chartAt Plane (T.chart p.1.1 : S)).symm z ∈
        T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
          T.caps T.region p.1.1 ↔
        0 ≤ B.ambientEndpointCut false z ∨ B.ambientEndpointTop false z ≤ 0 := by
  have hqs := (T.leftCap p).attachment_mem_chart_target ⟨T.length_pos.le, hr.le⟩
  have hg := (T.collar_germ_at_first_upper_attachment p hr).comp_tendsto
    ((chartAt Plane (T.chart p.1.1 : S)).symm.continuousAt hqs)
  have hc := T.cap_carrier_subset_region_chart_source
    (T.decomposition.edgeEndpoint p.1.2 false) (T.leftCap p).sector
  rw [(T.leftCap p).sector_region] at hc
  have hs := union_subset hc
    (T.bands p (T.graphs p).firstPiece).carrier_subset_region_chart_target
  filter_upwards [hg, T.first_cap_band_attachment_germ p hr,
    (chartAt Plane (T.chart p.1.1 : S)).open_target.mem_nhds hqs] with z hz hf hzs
  exact (Iff.of_eq hz).trans ((preimage_membership_iff_image
    (chartAt Plane (T.chart p.1.1 : S)) hs hzs).trans hf)



theorem coordinate_collar_last_upper_attachment_reflex_germ
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let B := T.bands p (T.graphs p).lastPiece
    ∀ᶠ z in 𝓝 (chartAt Plane (T.chart p.1.1 : S)
      (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
        T.length • (T.rightCap p).direction),
      (chartAt Plane (T.chart p.1.1 : S)).symm z ∈
        T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
          T.caps T.region p.1.1 ↔
        0 ≤ B.ambientEndpointCut true z ∨ B.ambientEndpointTop true z ≤ 0 := by
  have hqs := (T.rightCap p).attachment_mem_chart_target ⟨T.length_pos.le, hr.le⟩
  have hg := (T.collar_germ_at_last_upper_attachment p hr).comp_tendsto
    ((chartAt Plane (T.chart p.1.1 : S)).symm.continuousAt hqs)
  have hc := T.cap_carrier_subset_region_chart_source
    (T.decomposition.edgeEndpoint p.1.2 true) (T.rightCap p).sector
  rw [(T.rightCap p).sector_region] at hc
  have hs := union_subset hc
    (T.bands p (T.graphs p).lastPiece).carrier_subset_region_chart_target
  filter_upwards [hg, T.last_cap_band_attachment_germ p hr,
    (chartAt Plane (T.chart p.1.1 : S)).open_target.mem_nhds hqs] with z hz hf hzs
  exact (Iff.of_eq hz).trans ((preimage_membership_iff_image
    (chartAt Plane (T.chart p.1.1 : S)) hs hzs).trans hf)

end RetainedCoordinateTriangulation

end PoincareConjecture.Topology.Surface
