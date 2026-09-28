import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCoreGeometry
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CutGluing
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapGluing








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


theorem band_unique_away_from_endpoint_cuts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {q : S} (hq : q ∈ (T.bands p i).faces.carrier)
    (hl : q ∉ (T.bands p i).faces.leftCut)
    (hr : q ∉ (T.bands p i).faces.rightCut)
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
    · have hcut := T.band_adjacent p i j hnext
      have hright := (T.bands p i).rightCut_eq_segment ((T.graphs p).cut_lt i).le
      simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply] at hright
      exact False.elim (hr (hright.symm ▸ hcut ▸ (show q ∈
        (T.bands p i).faces.carrier ∩ (T.bands p j).faces.carrier from ⟨hq, ha⟩)))
    by_cases hprev : j.succ = i.castSucc
    · have hcut := T.band_adjacent p j i hprev
      have hleft := (T.bands p i).leftCut_eq_segment ((T.graphs p).cut_lt i).le
      simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply, ← hprev] at hleft
      exact False.elim (hl (hleft.symm ▸ hcut ▸ (show q ∈
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

omit [T2Space S] in

theorem first_band_leftCut_eq_chordSegment (p : T.decomposition.IncidentEdgeIndex) :
    (T.bands p (T.graphs p).firstPiece).faces.leftCut =
      (T.leftCap p).chordSegment T.length := by
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    (T.graphs p).firstPiece_castSucc, (T.graphs p).cut_first, (T.chains p).first,
    FiniteChartRegionDecomposition.CapGraphEndpoint.chordSegment,
    FiniteChartRegionDecomposition.edgeFromEndpoint, Bool.false_eq_true, ite_false,
    OpenPartialHomeomorph.symm_symm] using
    (T.bands p (T.graphs p).firstPiece).leftCut_eq_ray
      ((T.graphs p).cut_lt (T.graphs p).firstPiece).le

omit [T2Space S] in

theorem last_band_rightCut_eq_chordSegment (p : T.decomposition.IncidentEdgeIndex) :
    (T.bands p (T.graphs p).lastPiece).faces.rightCut =
      (T.rightCap p).chordSegment T.length := by
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    (T.graphs p).lastPiece_succ, (T.graphs p).cut_last, (T.chains p).last,
    FiniteChartRegionDecomposition.CapGraphEndpoint.chordSegment,
    FiniteChartRegionDecomposition.edgeFromEndpoint, ite_true,
    OpenPartialHomeomorph.symm_symm] using
    (T.bands p (T.graphs p).lastPiece).rightCut_eq_ray
      ((T.graphs p).cut_lt (T.graphs p).lastPiece).le

omit [T2Space S] in


theorem not_mem_region_caps_of_band_away_from_endpoint_cuts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {q : S} (hq : q ∈ (T.bands p i).faces.carrier)
    (hl : q ∉ (T.bands p i).faces.leftCut)
    (hr : q ∉ (T.bands p i).faces.rightCut) :
    q ∉ T.decomposition.vertexCapsInRegion T.caps T.region p.1.1 := by
  intro hc
  have h := T.band_caps p i ▸ (show q ∈ (T.bands p i).faces.carrier ∩
    T.decomposition.vertexCapsInRegion T.caps T.region p.1.1 from ⟨hq, hc⟩)
  rcases h with h | h
  · split_ifs at h with hi
    · subst i
      exact hl (T.first_band_leftCut_eq_chordSegment p ▸ h)
    · exact h
  · split_ifs at h with hi
    · subst i
      exact hr (T.last_band_rightCut_eq_chordSegment p ▸ h)
    · exact h



theorem collar_germ_of_band_away_from_endpoint_cuts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {q : S} (hq : q ∈ (T.bands p i).faces.carrier)
    (hl : q ∉ (T.bands p i).faces.leftCut)
    (hr : q ∉ (T.bands p i).faces.rightCut) :
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region p.1.1 =ᶠ[𝓝 q] (T.bands p i).faces.carrier := by
  let I := {a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs //
    a.1.1.1 = p.1.1}
  have hb : ∀ᶠ z in 𝓝 q, ∀ a : I, a.1 ≠ ⟨p, i⟩ →
      z ∉ (T.bands a.1.1 a.1.2).faces.carrier := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : a.1 = ⟨p, i⟩
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h ha))
    · have hn : q ∉ (T.bands a.1.1 a.1.2).faces.carrier := fun h =>
        ha (T.band_unique_away_from_endpoint_cuts p i hq hl hr a.1 a.2 h)
      filter_upwards [(T.bands a.1.1 a.1.2).faces.isClosed_carrier.isOpen_compl.mem_nhds hn]
        with z hz
      exact fun _ => hz
  have hc := (T.decomposition.isCompact_vertexCapsInRegion T.caps T.region p.1.1).isClosed.isOpen_compl.mem_nhds
    (T.not_mem_region_caps_of_band_away_from_endpoint_cuts p i hq hl hr)
  filter_upwards [hb, hc] with z hz hzc
  apply propext
  change (z ∈ T.decomposition.vertexCapsInRegion T.caps T.region p.1.1 ∪
    T.decomposition.graphBandsInRegion T.chart T.cut T.graphs T.chains T.bands p.1.1) ↔ _
  rw [mem_union, or_iff_right hzc]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_iUnion.mp h
    have he : a.1 = ⟨p, i⟩ := by_contra (fun hn => hz a hn ha)
    have he' := congrArg (fun b : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs =>
      (T.bands b.1 b.2).faces.carrier) he
    exact he' ▸ ha
  · intro h
    exact mem_iUnion.mpr ⟨⟨⟨p, i⟩, rfl⟩, h⟩



theorem coordinate_collar_germ_of_band_away_from_endpoint_cuts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {q : Plane} (hqs : q ∈ (chartAt Plane (T.chart p.1.1 : S)).target)
    (hq : (chartAt Plane (T.chart p.1.1 : S)).symm q ∈ (T.bands p i).faces.carrier)
    (hl : (chartAt Plane (T.chart p.1.1 : S)).symm q ∉ (T.bands p i).faces.leftCut)
    (hr : (chartAt Plane (T.chart p.1.1 : S)).symm q ∉ (T.bands p i).faces.rightCut) :
    (chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
        T.caps T.region p.1.1 =ᶠ[𝓝 q]
      (chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹' (T.bands p i).faces.carrier :=
  (T.collar_germ_of_band_away_from_endpoint_cuts p i hq hl hr).comp_tendsto
    ((chartAt Plane (T.chart p.1.1 : S)).symm.continuousAt hqs)

omit [T2Space S] in

theorem strip_point_not_mem_endpoint_cuts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {t z : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Icc 0 ((T.bands p i).faces.height t)) :
    ((T.graphs p).piece i).strip ((T.chains p).graphCuts i) (t, z) ∉
        (T.bands p i).faces.leftCut ∧
      ((T.graphs p).piece i).strip ((T.chains p).graphCuts i) (t, z) ∉
        (T.bands p i).faces.rightCut := by
  have hts : (t, z) ∈ (((T.graphs p).piece i).strip ((T.chains p).graphCuts i)).source :=
    (T.bands p i).subgraph_subset_source ⟨⟨ht.1.le, ht.2.le⟩, hz⟩
  constructor
  · intro h
    rw [← (T.bands p i).faces.left_height_image] at h
    obtain ⟨w, hw, he⟩ := h
    dsimp only at he
    rw [(T.bands p i).coordinates_eq] at he
    have hws : (0, w) ∈ (((T.graphs p).piece i).strip ((T.chains p).graphCuts i)).source :=
      (T.bands p i).subgraph_subset_source ⟨by simp, hw⟩
    have heq := (((T.graphs p).piece i).strip ((T.chains p).graphCuts i)).injOn hws hts he
    exact ht.1.ne (congrArg Prod.fst heq)
  · intro h
    rw [← (T.bands p i).faces.right_height_image] at h
    obtain ⟨w, hw, he⟩ := h
    dsimp only at he
    rw [(T.bands p i).coordinates_eq] at he
    have hws : (1, w) ∈ (((T.graphs p).piece i).strip ((T.chains p).graphCuts i)).source :=
      (T.bands p i).subgraph_subset_source ⟨by simp, hw⟩
    have heq := (((T.graphs p).piece i).strip ((T.chains p).graphCuts i)).injOn hws hts he
    exact ht.2.ne (congrArg Prod.fst heq).symm



theorem collar_germ_at_interior_strip_point
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {t z : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Icc 0 ((T.bands p i).faces.height t)) :
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region p.1.1 =ᶠ[𝓝 (((T.graphs p).piece i).strip
        ((T.chains p).graphCuts i) (t, z))] (T.bands p i).faces.carrier := by
  have hn := T.strip_point_not_mem_endpoint_cuts p i ht hz
  apply T.collar_germ_of_band_away_from_endpoint_cuts p i _ hn.1 hn.2
  rw [(T.bands p i).carrier_eq_fixed_strip]
  exact mem_image_of_mem _ ⟨⟨ht.1.le, ht.2.le⟩, hz⟩

omit [T2Space S] in


theorem band_positive_height_mem_region
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {t z : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hz : 0 < z) (hzh : z ≤ (T.bands p i).faces.height t) :
    ((T.graphs p).piece i).strip ((T.chains p).graphCuts i) (t, z) ∈
      connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
        T.decomposition.radius)ᶜ p.1.1 := by
  have hcarrier : ((T.graphs p).piece i).strip ((T.chains p).graphCuts i) (t, z) ∈
      (T.bands p i).faces.carrier := by
    rw [(T.bands p i).carrier_eq_fixed_strip]
    exact mem_image_of_mem _ ⟨ht, hz.le, hzh⟩
  apply T.decomposition.region_closure_diff_arrangement_subset p.1.1
    ⟨T.band_regions p i hcarrier, ?_⟩
  intro hK
  have hbase := T.band_boundary p i ▸ (show
    ((T.graphs p).piece i).strip ((T.chains p).graphCuts i) (t, z) ∈
      (T.bands p i).faces.carrier ∩ chartDiskBoundaryUnion T.decomposition.centers
        T.decomposition.radius from ⟨hcarrier, hK⟩)
  rw [← ((T.graphs p).piece i).strip_axis_image ((T.chains p).graphCuts i)
    ((T.graphs p).cut_lt i)] at hbase
  obtain ⟨s, hs, he⟩ := hbase
  have hts := (T.bands p i).subgraph_subset_source (show
    (t, z) ∈ {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧
      0 ≤ q.2 ∧ q.2 ≤ (T.bands p i).faces.height q.1} from ⟨ht, hz.le, hzh⟩)
  have hss := ((T.graphs p).piece i).strip_axis_mem_source ((T.chains p).graphCuts i)
    ((T.graphs p).cut_lt i) hs
  have heq := (((T.graphs p).piece i).strip ((T.chains p).graphCuts i)).injOn hss hts he
  exact hz.ne (congrArg Prod.snd heq)

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
