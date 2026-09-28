import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapBandCutFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapInteriorFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapTipExclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

def IsTrimTip (q : S) : Prop :=
  ∃ (e : T.decomposition.EdgeIndex) (terminal : Bool),
    q = T.decomposition.edgeFromEndpoint e terminal (T.cut e terminal)

def IsCapOuterTip (p : T.decomposition.vertices) (q : S) : Prop :=
  (∃ i, q = (T.caps p).firstOuterTip i) ∨ ∃ i, q = (T.caps p).secondOuterTip i

def capBandAttachmentTop (a : T.decomposition.IncidentEdgeIndex) (terminal : Bool) : S :=
  (chartAt Plane (T.chart a.1.1 : S)).symm
    (chartAt Plane (T.chart a.1.1 : S)
      (T.decomposition.edgeFromEndpoint a.1.2 terminal (T.cut a.1.2 terminal)) +
        T.length • (if terminal then (T.rightCap a).direction else (T.leftCap a).direction))

omit [T2Space S] in

theorem cap_band_region_eq_of_not_mem_arrangement
    (p : T.decomposition.vertices) (s : Bool × Bool)
    (a : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs a).count)
    {q : S} (hc : q ∈ ((T.caps p).face s).carrier)
    (hb : q ∈ (T.bands a i).faces.carrier)
    (hK : q ∉ chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius) :
    T.region p s = a.1.1 := by
  have hregion := T.decomposition.region_closure_diff_arrangement_subset a.1.1
    ⟨T.band_regions a i hb, hK⟩
  by_contra hne
  exact disjoint_left.mp (T.decomposition.region_disjoint_closure (Ne.symm hne))
    hregion (T.cap_regions p s hc)

omit [T2Space S] in

theorem cap_band_contact_mem_attachment_of_not_mem_arrangement
    (p : T.decomposition.vertices) (s : Bool × Bool)
    (a : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs a).count)
    {q : S} (hc : q ∈ ((T.caps p).face s).carrier)
    (hb : q ∈ (T.bands a i).faces.carrier)
    (hK : q ∉ chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius) :
    (i = (T.graphs a).firstPiece ∧ q ∈ (T.leftCap a).chordSegment T.length) ∨
      (i = (T.graphs a).lastPiece ∧ q ∈ (T.rightCap a).chordSegment T.length) := by
  have hR := T.cap_band_region_eq_of_not_mem_arrangement p s a i hc hb hK
  have hcap : q ∈ T.decomposition.vertexCapsInRegion T.caps T.region a.1.1 :=
    mem_iUnion.mpr ⟨⟨(p, s), hR⟩, hc⟩
  have h := T.band_caps a i ▸ (show q ∈ (T.bands a i).faces.carrier ∩
    T.decomposition.vertexCapsInRegion T.caps T.region a.1.1 from ⟨hb, hcap⟩)
  rcases h with h | h
  · split_ifs at h with hi
    · exact Or.inl ⟨hi, h⟩
    · exact False.elim h
  · split_ifs at h with hi
    · exact Or.inr ⟨hi, h⟩
    · exact False.elim h

omit [T2Space S] in

theorem cap_band_arrangement_contact_isTrimTip
    (p : T.decomposition.vertices) (s : Bool × Bool)
    (htrim : ∀ e : T.decomposition.EdgeIndex,
      Disjoint ((T.caps p).face s).carrier
        ((T.decomposition.edge e.1 e.2).map '' Ioo (T.cut e false) (1 - T.cut e true)))
    (a : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs a).count)
    {q : S} (hc : q ∈ ((T.caps p).face s).carrier)
    (hb : q ∈ (T.bands a i).faces.carrier)
    (hK : q ∈ chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius) :
    T.IsTrimTip q := by
  have h := T.band_boundary a i ▸ (show q ∈ (T.bands a i).faces.carrier ∩
    chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius from ⟨hb, hK⟩)
  obtain ⟨t, ht, htq⟩ := h
  have hlo : T.cut a.1.2 false ≤ t := by
    have h := (T.graphs a).cut_strictMono.monotone (Fin.zero_le i.castSucc)
    rw [(T.graphs a).cut_first] at h
    exact h.trans ht.1
  have hhi : t ≤ 1 - T.cut a.1.2 true := by
    have h := (T.graphs a).cut_strictMono.monotone (Fin.le_last i.succ)
    rw [(T.graphs a).cut_last] at h
    exact ht.2.trans h
  by_cases hleft : t = T.cut a.1.2 false
  · exact ⟨a.1.2, false, by simpa only [hleft,
      FiniteChartRegionDecomposition.edgeFromEndpoint, Bool.false_eq_true, ite_false] using htq.symm⟩
  by_cases hright : t = 1 - T.cut a.1.2 true
  · exact ⟨a.1.2, true, by simpa only [hright,
      FiniteChartRegionDecomposition.edgeFromEndpoint, ite_true] using htq.symm⟩
  exact False.elim (disjoint_left.mp (htrim a.1.2) hc
    ⟨t, ⟨lt_of_le_of_ne hlo (Ne.symm hleft), lt_of_le_of_ne hhi hright⟩, htq⟩)

theorem left_attachment_point_cases (a : T.decomposition.IncidentEdgeIndex)
    {q : S} (hq : q ∈ (T.leftCap a).chordSegment T.length) :
    T.IsTrimTip q ∨ q ∈ (T.leftCap a).openChordSegment T.length ∨
      q = T.capBandAttachmentTop a false := by
  obtain ⟨u, hu, huq⟩ := hq
  by_cases hzero : u = 0
  · subst u
    left
    refine ⟨a.1.2, false, ?_⟩
    have hs : T.decomposition.edgeFromEndpoint a.1.2 false (T.cut a.1.2 false) ∈
        (chartAt Plane (T.chart a.1.1 : S)).source := by
      apply T.chart_source a.1.1
      have h := T.cap_regions _ _ (T.leftCap a).tip_mem_cap
      simpa only [(T.leftCap a).sector_region] using h
    simpa only [zero_smul, add_zero, (chartAt Plane (T.chart a.1.1 : S)).left_inv hs] using huq.symm
  by_cases htop : u = T.length
  · right; right
    simpa only [htop, capBandAttachmentTop, Bool.false_eq_true, ite_false] using huq.symm
  · exact Or.inr (Or.inl ⟨u,
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero), lt_of_le_of_ne hu.2 htop⟩, huq⟩)

theorem right_attachment_point_cases (a : T.decomposition.IncidentEdgeIndex)
    {q : S} (hq : q ∈ (T.rightCap a).chordSegment T.length) :
    T.IsTrimTip q ∨ q ∈ (T.rightCap a).openChordSegment T.length ∨
      q = T.capBandAttachmentTop a true := by
  obtain ⟨u, hu, huq⟩ := hq
  by_cases hzero : u = 0
  · subst u
    left
    refine ⟨a.1.2, true, ?_⟩
    have hs : T.decomposition.edgeFromEndpoint a.1.2 true (T.cut a.1.2 true) ∈
        (chartAt Plane (T.chart a.1.1 : S)).source := by
      apply T.chart_source a.1.1
      have h := T.cap_regions _ _ (T.rightCap a).tip_mem_cap
      simpa only [(T.rightCap a).sector_region] using h
    simpa only [zero_smul, add_zero, (chartAt Plane (T.chart a.1.1 : S)).left_inv hs] using huq.symm
  by_cases htop : u = T.length
  · right; right
    simpa only [htop, capBandAttachmentTop, ite_true] using huq.symm
  · exact Or.inr (Or.inl ⟨u,
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero), lt_of_le_of_ne hu.2 htop⟩, huq⟩)

omit [T2Space S] in

theorem cap_chord_endpoint_isOuterTip (p : T.decomposition.vertices) (s : Bool × Bool)
    (terminal : Bool) :
    T.IsCapOuterTip p ((((T.caps p).face s).boundary 0).map (if terminal then 1 else 0)) := by
  cases terminal
  · left
    refine ⟨s.1, ?_⟩
    rw [(T.caps p).boundary_map]
    simpa [affineChartSegment, Fin.succAbove] using
      (T.caps p).coordinate_first_outer_tip s.1 s.2
  · right
    refine ⟨s.2, ?_⟩
    rw [(T.caps p).boundary_map]
    simpa [affineChartSegment, Fin.succAbove] using
      (T.caps p).coordinate_second_outer_tip s.2 s.1

theorem cap_point_open_chord_of_not_interior_not_tip
    (p : T.decomposition.vertices) {q : S}
    (hq : ∃ s, q ∈ ((T.caps p).face s).carrier)
    (hint : q ∉ interior (⋃ s, ((T.caps p).face s).carrier))
    (htip : ¬ T.IsCapOuterTip p q) :
    ∃ (s : Bool × Bool) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧
      (((T.caps p).face s).boundary 0).map t = q := by
  have hfront : q ∈ frontier (⋃ s, ((T.caps p).face s).carrier) :=
    ⟨subset_closure (mem_iUnion.mpr hq), hint⟩
  obtain ⟨s, t, ht, htq⟩ := mem_iUnion.mp ((T.caps p).frontier_union_subset_chords hfront)
  have hzero : t ≠ 0 := by
    intro he
    subst t
    apply htip
    exact htq ▸ T.cap_chord_endpoint_isOuterTip p s false
  have hone : t ≠ 1 := by
    intro he
    subst t
    apply htip
    exact htq ▸ T.cap_chord_endpoint_isOuterTip p s true
  exact ⟨s, t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩, htq⟩

theorem cap_outer_tip_not_mem_open_chord (p : T.decomposition.vertices) {q : S}
    (hq : T.IsCapOuterTip p q) (v : T.decomposition.vertices) (s : Bool × Bool) :
    q ∉ (((T.caps v).face s).boundary 0).map '' Ioo (0 : ℝ) 1 := by
  rintro ⟨t, ht, htq⟩
  rcases hq with ⟨i, hi⟩ | ⟨i, hi⟩
  · have htrue := T.cap_unique_at_open_chord v s ht p (i, true) (by
      rw [htq, hi]
      exact ((T.caps p).firstOuterTip_mem_carrier_iff i (i, true)).mpr rfl)
    have hfalse := T.cap_unique_at_open_chord v s ht p (i, false) (by
      rw [htq, hi]
      exact ((T.caps p).firstOuterTip_mem_carrier_iff i (i, false)).mpr rfl)
    have he := congrArg Prod.snd (htrue.2.trans hfalse.2.symm)
    exact Bool.noConfusion he
  · have htrue := T.cap_unique_at_open_chord v s ht p (true, i) (by
      rw [htq, hi]
      exact ((T.caps p).secondOuterTip_mem_carrier_iff i (true, i)).mpr rfl)
    have hfalse := T.cap_unique_at_open_chord v s ht p (false, i) (by
      rw [htq, hi]
      exact ((T.caps p).secondOuterTip_mem_carrier_iff i (false, i)).mpr rfl)
    have he := congrArg Prod.fst (htrue.2.trans hfalse.2.symm)
    exact Bool.noConfusion he

theorem cap_outer_tip_not_mem_bands (p : T.decomposition.vertices)
    (hr : T.length < 1)
    (htrim : ∀ (s : Bool × Bool) (e : T.decomposition.EdgeIndex),
      Disjoint ((T.caps p).face s).carrier
        ((T.decomposition.edge e.1 e.2).map '' Ioo (T.cut e false) (1 - T.cut e true)))
    {q : S} (hq : T.IsCapOuterTip p q) (hntip : ¬ T.IsTrimTip q)
    (a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs) :
    q ∉ (T.bands a.1 a.2).faces.carrier := by
  intro ha
  have hc : ∃ s, q ∈ ((T.caps p).face s).carrier := by
    rcases hq with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨(i, true), hi ▸ ((T.caps p).firstOuterTip_mem_carrier_iff i (i, true)).mpr rfl⟩
    · exact ⟨(true, i), hi ▸ ((T.caps p).secondOuterTip_mem_carrier_iff i (true, i)).mpr rfl⟩
  obtain ⟨s, hs⟩ := hc
  have hK : q ∉ chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius := by
    intro h
    exact hntip (T.cap_band_arrangement_contact_isTrimTip p s (htrim s) a.1 a.2 hs ha h)
  rcases T.cap_band_contact_mem_attachment_of_not_mem_arrangement p s a.1 a.2 hs ha hK with
    ⟨_, hleft⟩ | ⟨_, hright⟩
  · rcases T.left_attachment_point_cases a.1 hleft with h | h | h
    · exact hntip h
    · exact T.cap_outer_tip_not_mem_open_chord p hq _ _
        ((T.leftCap a.1).openChordSegment_subset_open_chord T.length_le_one h)
    · apply T.cap_outer_tip_not_mem_open_chord p hq
        (T.decomposition.edgeEndpoint a.1.1.2 false) (T.leftCap a.1).sector
      apply (T.leftCap a.1).openChordSegment_subset_open_chord (r := 1) le_rfl
      exact ⟨T.length, ⟨T.length_pos, hr⟩, by simpa only [capBandAttachmentTop,
        Bool.false_eq_true, ite_false] using h.symm⟩
  · rcases T.right_attachment_point_cases a.1 hright with h | h | h
    · exact hntip h
    · exact T.cap_outer_tip_not_mem_open_chord p hq _ _
        ((T.rightCap a.1).openChordSegment_subset_open_chord T.length_le_one h)
    · apply T.cap_outer_tip_not_mem_open_chord p hq
        (T.decomposition.edgeEndpoint a.1.1.2 true) (T.rightCap a.1).sector
      apply (T.rightCap a.1).openChordSegment_subset_open_chord (r := 1) le_rfl
      exact ⟨T.length, ⟨T.length_pos, hr⟩, by simpa only [capBandAttachmentTop,
        ite_true] using h.symm⟩

theorem exists_core_of_cap_union_boundary_not_mem_bands
    (p : T.decomposition.vertices) {q : S}
    (hq : ∃ s, q ∈ ((T.caps p).face s).carrier)
    (hint : q ∉ interior (⋃ s, ((T.caps p).face s).carrier))
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      q ∉ (T.bands a.1 a.2).faces.carrier) :
    ∃ R : T.decomposition.regions,
      q ∈ (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support ∧
      ∀ s, q ∈ ((T.caps p).face s).carrier → T.region p s = R := by
  have hex : ∃ R : T.decomposition.regions,
      q ∈ (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support := by
    by_contra hn
    push Not at hn
    have hcore : ∀ᶠ z in 𝓝 q, ∀ R : T.decomposition.regions, z ∉
        (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support := by
      apply Filter.eventually_all.mpr
      intro R
      have hc : IsClosed ((chartAt Plane (T.chart R : S)).symm ''
          (T.refined.mesh R).toPlaneComplex.support) := by
        rw [T.refined_core_back R]
        exact isClosed_closure
      exact hc.isOpen_compl.mem_nhds (hn R)
    have hcaps : ∀ᶠ z in 𝓝 q, ∀ a : T.decomposition.vertices × (Bool × Bool),
        a.1 ≠ p → z ∉ ((T.caps a.1).face a.2).carrier := by
      apply Filter.eventually_all.mpr
      intro a
      by_cases ha : a.1 = p
      · exact Filter.Eventually.of_forall (fun _ h => False.elim (h ha))
      · have hnot : q ∉ ((T.caps a.1).face a.2).carrier := by
          intro h
          obtain ⟨s, hs⟩ := hq
          exact disjoint_left.mp (T.caps_disjoint_of_vertices_ne a.1 p ha a.2 s) h hs
        filter_upwards [((T.caps a.1).face a.2).isClosed_carrier.isOpen_compl.mem_nhds hnot]
          with z hz
        exact fun _ => hz
    have hbands : ∀ᶠ z in 𝓝 q,
        ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
          z ∉ (T.bands a.1 a.2).faces.carrier := by
      apply Filter.eventually_all.mpr
      intro a
      exact (T.bands a.1 a.2).faces.isClosed_carrier.isOpen_compl.mem_nhds (hband a)
    apply hint
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hcore, hcaps, hbands] with z hzcore hzcaps hzbands
    have hcover : z ∈ ⋃ R ∈ T.decomposition.regions, closure (connectedComponentIn
        (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R) := by
      rw [T.decomposition.region_closure_cover]
      trivial
    obtain ⟨R, hR, hRz⟩ := mem_iUnion₂.mp hcover
    rw [T.refined.cover ⟨R, hR⟩] at hRz
    rcases hRz with (hc | hb) | hk
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hc
      have he : a.1.1 = p := by_contra (fun h => hzcaps a.1 h ha)
      have he' := congrArg (fun v : T.decomposition.vertices =>
        ((T.caps v).face a.1.2).carrier) he
      exact mem_iUnion.mpr ⟨a.1.2, he' ▸ ha⟩
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hb
      exact False.elim (hzbands a.1 ha)
    · exact False.elim (hzcore ⟨R, hR⟩ hk)
  obtain ⟨R, hR⟩ := hex
  refine ⟨R, hR, ?_⟩
  intro s hs
  by_contra hne
  exact disjoint_left.mp (T.decomposition.region_disjoint_closure (Ne.symm hne))
    (T.refined.in_region R hR) (T.cap_regions p s hs)

theorem unmatched_cap_outer_tip_core_incidence (p : T.decomposition.vertices)
    (hr : T.length < 1)
    (htrim : ∀ (s : Bool × Bool) (e : T.decomposition.EdgeIndex),
      Disjoint ((T.caps p).face s).carrier
        ((T.decomposition.edge e.1 e.2).map '' Ioo (T.cut e false) (1 - T.cut e true)))
    {q : S} (hq : T.IsCapOuterTip p q) (hntip : ¬ T.IsTrimTip q)
    (hint : q ∉ interior (⋃ s, ((T.caps p).face s).carrier)) :
    ∃ R : T.decomposition.regions,
      q ∈ (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support ∧
      q ∈ connectedComponentIn
        (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R ∧
      (∀ s, q ∈ ((T.caps p).face s).carrier → T.region p s = R) ∧
      ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
        q ∉ (T.bands a.1 a.2).faces.carrier := by
  have hb := T.cap_outer_tip_not_mem_bands p hr htrim hq hntip
  have hc : ∃ s, q ∈ ((T.caps p).face s).carrier := by
    rcases hq with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨(i, true), hi ▸ ((T.caps p).firstOuterTip_mem_carrier_iff i (i, true)).mpr rfl⟩
    · exact ⟨(true, i), hi ▸ ((T.caps p).secondOuterTip_mem_carrier_iff i (true, i)).mpr rfl⟩
  obtain ⟨R, hR, hregions⟩ := T.exists_core_of_cap_union_boundary_not_mem_bands p hc hint hb
  exact ⟨R, hR, T.refined.in_region R hR, hregions, hb⟩

theorem cap_point_cases (p : T.decomposition.vertices)
    (htrim : ∀ (s : Bool × Bool) (e : T.decomposition.EdgeIndex),
      Disjoint ((T.caps p).face s).carrier
        ((T.decomposition.edge e.1 e.2).map '' Ioo (T.cut e false) (1 - T.cut e true)))
    {q : S} (hq : ∃ s, q ∈ ((T.caps p).face s).carrier) :
    q ∈ interior (⋃ s, ((T.caps p).face s).carrier) ∨
      T.IsTrimTip q ∨
      (T.IsCapOuterTip p q ∧ ¬ T.IsTrimTip q ∧
        q ∉ interior (⋃ s, ((T.caps p).face s).carrier)) ∨
      (∃ (s : Bool × Bool) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧
        (((T.caps p).face s).boundary 0).map t = q ∧
        ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
          q ∉ (T.bands a.1 a.2).faces.carrier) ∨
      (∃ a : T.decomposition.IncidentEdgeIndex,
        q ∈ (T.leftCap a).openChordSegment T.length ∨
          q ∈ (T.rightCap a).openChordSegment T.length) ∨
      ∃ (a : T.decomposition.IncidentEdgeIndex) (terminal : Bool),
        q = T.capBandAttachmentTop a terminal := by
  by_cases hint : q ∈ interior (⋃ s, ((T.caps p).face s).carrier)
  · exact Or.inl hint
  right
  by_cases htip : T.IsTrimTip q
  · exact Or.inl htip
  right
  by_cases houter : T.IsCapOuterTip p q
  · exact Or.inl ⟨houter, htip, hint⟩
  right
  obtain ⟨s, t, ht, htq⟩ := T.cap_point_open_chord_of_not_interior_not_tip p hq hint houter
  by_cases hb : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      q ∉ (T.bands a.1 a.2).faces.carrier
  · exact Or.inl ⟨s, t, ht, htq, hb⟩
  right
  push Not at hb
  obtain ⟨a, ha⟩ := hb
  have hc : q ∈ ((T.caps p).face s).carrier :=
    htq ▸ (((T.caps p).open_chord_mem_carrier_iff s s ht).mpr rfl)
  have hK : q ∉ chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius := by
    intro h
    exact htip (T.cap_band_arrangement_contact_isTrimTip p s (htrim s) a.1 a.2 hc ha h)
  rcases T.cap_band_contact_mem_attachment_of_not_mem_arrangement p s a.1 a.2 hc ha hK with
    ⟨_, hleft⟩ | ⟨_, hright⟩
  · rcases T.left_attachment_point_cases a.1 hleft with h | h | h
    · exact False.elim (htip h)
    · exact Or.inl ⟨a.1, Or.inl h⟩
    · exact Or.inr ⟨a.1, false, h⟩
  · rcases T.right_attachment_point_cases a.1 hright with h | h | h
    · exact False.elim (htip h)
    · exact Or.inl ⟨a.1, Or.inr h⟩
    · exact Or.inr ⟨a.1, true, h⟩

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
