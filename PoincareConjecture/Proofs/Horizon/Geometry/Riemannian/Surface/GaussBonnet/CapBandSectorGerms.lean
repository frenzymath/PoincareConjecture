import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapChordHalfspaces
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.ChainSectorGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilySeparation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAssembly








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

private theorem interior_partial_coordinate_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : OpenPartialHomeomorph X Y) {K : Set X} (hK : K ⊆ F.source) :
    interior (F '' K) = F '' interior K := by
  have himage : F '' K ⊆ F.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact F.map_source (hK hz)
  have hrel : F.IsImage K (F '' K) := by
    intro z hz
    constructor
    · rintro ⟨w, hw, heq⟩
      exact F.injOn (hK hw) hz heq ▸ hw
    · exact mem_image_of_mem F
  simpa only [inter_eq_right.mpr (interior_subset.trans hK),
    inter_eq_right.mpr (interior_subset.trans himage)] using hrel.interior.image_eq.symm

private theorem image_mem_closure_interior_of_regular
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : OpenPartialHomeomorph X Y) {K : Set X} (hK : K ⊆ F.source)
    (hregular : closure (interior K) = K) {q : Y} (hq : q ∈ F '' K) :
    q ∈ closure (interior (F '' K)) := by
  rw [interior_partial_coordinate_image F hK]
  have hsource : closure (interior K) ⊆ F.source := by rw [hregular]; exact hK
  have h := (F.continuousOn.mono hsource).image_closure
  rw [hregular] at h
  exact h hq

private theorem disjoint_coordinate_image_interior
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : OpenPartialHomeomorph X Y) {A B : Set X}
    (hA : A ⊆ F.source) (hB : B ⊆ F.source) (hdisjoint : Disjoint A (interior B)) :
    Disjoint (F '' A) (interior (F '' B)) := by
  rw [interior_partial_coordinate_image F hB]
  apply disjoint_left.mpr
  rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
  have hab := F.injOn (hA ha) (hB (interior_subset hb)) (haz.trans hbz.symm)
  exact disjoint_left.mp hdisjoint (hab ▸ ha) hb



theorem halfplane_side_of_regular_wedge_separation
    {A B : Set Plane} {q d : Plane} (l f g : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hf : Function.Surjective f)
    (hd : d ≠ 0) (hlq : l q = 0) (hfq : f q = 0)
    (hld : l.linear d = 0) (hfd : f.linear d = 0)
    (hA : ∀ᶠ z in 𝓝 q, z ∈ A ↔ l z ≤ 0)
    (hB : ∀ᶠ z in 𝓝 q, z ∈ B ↔ f z ≤ 0 ∧ g z ≤ 0)
    (hregular : q ∈ closure (interior B)) (hdisjoint : Disjoint A (interior B)) :
    (∃ c : ℝ, c < 0 ∧ l = c • f) ∧
      (∀ᶠ z in 𝓝 q, z ∈ A ↔ 0 ≤ f z) ∧
      ∀ᶠ z in 𝓝 q, z ∈ A ∪ B ↔ 0 ≤ f z ∨ g z ≤ 0 := by
  obtain ⟨c, hc, he⟩ := affine_functionals_eq_smul_of_common_line f l hf hl hd hfq hlq hfd hld
  have hcneg : c < 0 := by
    by_contra hn
    have hcpos : 0 < c := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hc)
    have hnot : ∀ᶠ z in 𝓝 q, z ∉ interior B := by
      filter_upwards [hA, hB] with z hzA hzB hz
      have hfz := ((hzB.mp (interior_subset hz)).1)
      have hlz : l z ≤ 0 := by
        rw [he]
        exact mul_nonpos_of_nonneg_of_nonpos hcpos.le hfz
      exact disjoint_left.mp hdisjoint (hzA.mpr hlz) hz
    exact (mem_closure_iff_frequently.mp hregular) hnot
  have hcap : ∀ᶠ z in 𝓝 q, z ∈ A ↔ 0 ≤ f z := by
    filter_upwards [hA] with z hz
    rw [hz, he]
    change c * f z ≤ 0 ↔ 0 ≤ f z
    constructor <;> intro h <;> nlinarith
  refine ⟨⟨c, hcneg, he⟩, hcap, ?_⟩
  filter_upwards [hcap, hB] with z hzA hzB
  rw [mem_union, hzA, hzB]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · rcases le_total 0 (f z) with hfz | hfz
      · exact Or.inl hfz
      · exact Or.inr ⟨hfz, h⟩

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



theorem exists_attachment_chart_cap_halfplane {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    let q := chartAt Plane (chart R) (D.edgeFromEndpoint e terminal trim) + r • E.direction
    ∃ l : Plane →ᵃ[ℝ] ℝ, Function.Surjective l ∧ l q = 0 ∧ l.linear E.direction = 0 ∧
      ∀ᶠ z in 𝓝 q,
        z ∈ chartAt Plane (chart R) '' ((caps (D.edgeEndpoint e terminal)).face E.sector).carrier ↔
          l z ≤ 0 := by
  let v := decide (E.radialEdge = 1)
  let t := if v then 1 - r else r
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    dsimp only [t]
    split <;> constructor <;> linarith [hr.1, hr.2]
  let C := caps (D.edgeEndpoint e terminal)
  have hpoint : chartAt Plane (chart R) (D.edgeFromEndpoint e terminal trim) + r • E.direction =
      (1 - t) • C.planarCoordinates E.sector (C.scale, 0) +
        t • C.planarCoordinates E.sector (0, C.scale) := by
    rw [← E.chord_base, E.direction_eq]
    exact C.chord_ray_eq_affine E.sector v r
  obtain ⟨l, hl, hlq, hld, hcap⟩ := C.exists_chart_carrier_chord_affine_halfspace E.sector ht
  rw [← hpoint] at hlq hcap
  refine ⟨l, hl, hlq, ?_, ?_⟩
  · rw [E.direction_eq]
    unfold ChartCircleArrangementVertexPatch.VertexCapFaces.chordDirection
    split
    · have hrev : C.planarCoordinates E.sector (C.scale, 0) -
          C.planarCoordinates E.sector (0, C.scale) =
        -(C.planarCoordinates E.sector (0, C.scale) -
          C.planarCoordinates E.sector (C.scale, 0)) := by abel
      rw [hrev, map_neg, hld, neg_zero]
    · exact hld
  · simpa only [E.sector_region] using hcap

end FiniteChartRegionDecomposition.CapGraphEndpoint

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {D : FiniteChartRegionDecomposition (M := S)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane S} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

theorem ambientEndpointCut_surjective (right : Bool) :
    Function.Surjective (B.ambientEndpointCut right) := by
  apply (AffineMap.linear_surjective_iff _).mp
  apply LinearMap.surjective
  intro hz
  apply B.faces.endpointCutFunctional_linear_ne_zero right
  ext v
  have h := congrArg (fun L : Plane →ₗ[ℝ] ℝ => L (G.frame.symm (collarParameterEquiv v))) hz
  change (B.faces.endpointCutFunctional right).linear
    (collarParameterEquiv.symm (G.frame (G.frame.symm (collarParameterEquiv v)))) = 0 at h
  simpa only [G.frame.apply_symm_apply, collarParameterEquiv.symm_apply_apply,
    LinearMap.zero_apply] using h

theorem carrier_subset_region_chart_target : B.faces.carrier ⊆ C.target := by
  intro q hq
  exact (B.faces.carrier_subset_target hq).1.1

theorem ambientEndpointCut_direction (right : Bool) :
    (B.ambientEndpointCut right).linear
      (G.frame.symm (if right then (ub, wb) else (ua, wa))) = 0 := by
  rw [B.ambientEndpointCut_linear_apply, G.frame.apply_symm_apply]
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

theorem ambient_first_endpoint_functionals_vanish (hab : a ≤ b) :
    let q := C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)
    B.ambientEndpointCut false q = 0 ∧ B.ambientEndpointTop false q = 0 := by
  constructor
  · change B.faces.endpointCutFunctional false (collarParameterEquiv.symm (G.frame _)) = 0
    rw [B.ambient_first_vertex hab]
    exact B.faces.endpointCutFunctional_first_vertex
  · change B.faces.topLineFunctional B.faces.firstCell (collarParameterEquiv.symm (G.frame _)) = 0
    rw [B.ambient_first_vertex hab]
    exact B.faces.topLineFunctional_left_vertex B.faces.firstCell

theorem ambient_last_endpoint_functionals_vanish (hab : a ≤ b) :
    let q := C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb)
    B.ambientEndpointCut true q = 0 ∧ B.ambientEndpointTop true q = 0 := by
  constructor
  · change B.faces.endpointCutFunctional true (collarParameterEquiv.symm (G.frame _)) = 0
    rw [B.ambient_last_vertex hab]
    exact B.faces.endpointCutFunctional_last_vertex
  · change B.faces.topLineFunctional B.faces.lastCell (collarParameterEquiv.symm (G.frame _)) = 0
    rw [B.ambient_last_vertex hab]
    have hi : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
      apply Fin.ext
      change B.faces.interface.count - 1 + 1 = B.faces.interface.count
      have hp := B.faces.interface.count_pos
      omega
    simpa only [hi, ObliqueBandFaces.planarTopVertex] using
      B.faces.topLineFunctional_right_vertex B.faces.lastCell

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

namespace FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {D : FiniteChartRegionDecomposition (M := S)}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : S)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → S}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions} {cut : D.EdgeIndex → Bool → ℝ}
  {Q : D.OrientedEdgeGraphSubdivision e R (chartAt Plane (chart R)).symm
    (cut e false) (1 - cut e true)}
  (L : D.CapGraphEndpoint P region chart caps e R (Q.piece Q.firstPiece) false (cut e false))
  (E : D.CapGraphEndpoint P region chart caps e R (Q.piece Q.lastPiece) true (cut e true))
  (K : Q.CutChain L.direction E.direction)
  {δ r : ℝ}



theorem first_attachment_union_reflex_germ
    (B : (Q.piece Q.firstPiece).FixedStripBandFaces (K.graphCuts Q.firstPiece) δ r r)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hdisjoint : Disjoint ((caps (D.edgeEndpoint e false)).face L.sector).carrier
      (interior B.faces.carrier)) :
    ∀ᶠ z in 𝓝 (chartAt Plane (chart R) (D.edgeFromEndpoint e false (cut e false)) + r • L.direction),
      z ∈ chartAt Plane (chart R) ''
        (((caps (D.edgeEndpoint e false)).face L.sector).carrier ∪ B.faces.carrier) ↔
          0 ≤ B.ambientEndpointCut false z ∨ B.ambientEndpointTop false z ≤ 0 := by
  obtain ⟨l, hl, hlq, hld, hcap⟩ := L.exists_attachment_chart_cap_halfplane hr
  have hband := B.ambient_carrier_first_top_eventually_iff (Q.cut_lt Q.firstPiece).le
  have hzero := B.ambient_first_endpoint_functionals_vanish (Q.cut_lt Q.firstPiece).le
  have hker := B.ambientEndpointCut_direction false
  simp only [Prod.eta, Bool.false_eq_true, ↓reduceIte, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, Q.firstPiece_castSucc, Q.cut_first, K.first] at hband hzero hker
  have hcap_source : ((caps (D.edgeEndpoint e false)).face L.sector).carrier ⊆
      (chartAt Plane (chart R)).source := by
    rw [(caps _).carrier_eq L.sector]
    rintro _ ⟨z, hz, rfl⟩
    have h := (caps _).coordinates_target L.sector
      (((caps _).coordinates L.sector).map_source ((caps _).triangle_subset_source L.sector hz))
    simpa only [L.sector_region] using h
  have hregular := image_mem_closure_interior_of_regular (chartAt Plane (chart R))
    B.carrier_subset_region_chart_target B.faces.closure_interior_carrier
    ((hband.self_of_nhds).mpr ⟨hzero.1.le, hzero.2.le⟩)
  have hsep := disjoint_coordinate_image_interior (chartAt Plane (chart R))
    hcap_source B.carrier_subset_region_chart_target hdisjoint
  have hresult := halfplane_side_of_regular_wedge_separation l
    (B.ambientEndpointCut false) (B.ambientEndpointTop false) hl
    (B.ambientEndpointCut_surjective false) L.direction_ne_zero hlq hzero.1
    hld hker hcap hband hregular hsep
  filter_upwards [hresult.2.2] with z hz
  simpa only [image_union] using hz



theorem last_attachment_union_reflex_germ
    (B : (Q.piece Q.lastPiece).FixedStripBandFaces (K.graphCuts Q.lastPiece) δ r r)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hdisjoint : Disjoint ((caps (D.edgeEndpoint e true)).face E.sector).carrier
      (interior B.faces.carrier)) :
    ∀ᶠ z in 𝓝 (chartAt Plane (chart R) (D.edgeFromEndpoint e true (cut e true)) + r • E.direction),
      z ∈ chartAt Plane (chart R) ''
        (((caps (D.edgeEndpoint e true)).face E.sector).carrier ∪ B.faces.carrier) ↔
          0 ≤ B.ambientEndpointCut true z ∨ B.ambientEndpointTop true z ≤ 0 := by
  obtain ⟨l, hl, hlq, hld, hcap⟩ := E.exists_attachment_chart_cap_halfplane hr
  have hband := B.ambient_carrier_last_top_eventually_iff (Q.cut_lt Q.lastPiece).le
  have hzero := B.ambient_last_endpoint_functionals_vanish (Q.cut_lt Q.lastPiece).le
  have hker := B.ambientEndpointCut_direction true
  simp only [Prod.eta, ↓reduceIte, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, Q.lastPiece_succ, Q.cut_last, K.last] at hband hzero hker
  have hcap_source : ((caps (D.edgeEndpoint e true)).face E.sector).carrier ⊆
      (chartAt Plane (chart R)).source := by
    rw [(caps _).carrier_eq E.sector]
    rintro _ ⟨z, hz, rfl⟩
    have h := (caps _).coordinates_target E.sector
      (((caps _).coordinates E.sector).map_source ((caps _).triangle_subset_source E.sector hz))
    simpa only [E.sector_region] using h
  have hregular := image_mem_closure_interior_of_regular (chartAt Plane (chart R))
    B.carrier_subset_region_chart_target B.faces.closure_interior_carrier
    ((hband.self_of_nhds).mpr ⟨hzero.1.le, hzero.2.le⟩)
  have hsep := disjoint_coordinate_image_interior (chartAt Plane (chart R))
    hcap_source B.carrier_subset_region_chart_target hdisjoint
  have hresult := halfplane_side_of_regular_wedge_separation l
    (B.ambientEndpointCut true) (B.ambientEndpointTop true) hl
    (B.ambientEndpointCut_surjective true) E.direction_ne_zero hlq hzero.1
    hld hker hcap hband hregular hsep
  filter_upwards [hresult.2.2] with z hz
  simpa only [image_union] using hz

end FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

namespace RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))



theorem cap_disjoint_band_interior (p : T.decomposition.vertices) (s : Bool × Bool)
    (a : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs a).count) :
    Disjoint ((T.caps p).face s).carrier (interior (T.bands a i).faces.carrier) := by
  have hunion :
      (⋃ j : Fin (T.bands a i).faces.interface.count × Bool,
        T.parentCoordinates (.inr (.inl ⟨⟨a, i⟩, j⟩)) ''
          (T.refinement.mesh (.inr (.inl ⟨⟨a, i⟩, j⟩))).toPlaneComplex.support) =
        (T.bands a i).faces.carrier := by
    change (⋃ j, _) = ⋃ j, ((T.bands a i).faces.face j).carrier
    apply iUnion_congr
    intro j
    rw [(T.refinement.subdivision (.inr (.inl ⟨⟨a, i⟩, j⟩))).support]
    exact ((T.bands a i).faces.face_carrier_eq_coordinates j).symm
  apply disjoint_left.mpr
  intro q hq hband
  have hn := coordinate_mesh_family_not_mem_of_interior_subfamily
    T.refinement.mesh T.parentCoordinates T.refinement.face
    (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
    T.refinement.intersection_frontier
    (fun j : Fin (T.bands a i).faces.interface.count × Bool =>
      (Sum.inr (Sum.inl ⟨⟨a, i⟩, j⟩) : T.Parent)) (.inl (p, s))
    (by intro j; simp) (hunion.symm ▸ hband)
  apply hn
  rw [(T.refinement.subdivision (.inl (p, s))).support]
  exact (T.caps p).carrier_eq s ▸ hq



theorem first_cap_band_attachment_germ (a : T.decomposition.IncidentEdgeIndex)
    (hr : T.length < 1) :
    let B := T.bands a (T.graphs a).firstPiece
    ∀ᶠ z in 𝓝 (chartAt Plane (T.chart a.1.1 : S)
      (T.decomposition.edgeFromEndpoint a.1.2 false (T.cut a.1.2 false)) +
        T.length • (T.leftCap a).direction),
      z ∈ chartAt Plane (T.chart a.1.1 : S) ''
        (((T.caps (T.decomposition.edgeEndpoint a.1.2 false)).face (T.leftCap a).sector).carrier ∪
          B.faces.carrier) ↔
            0 ≤ B.ambientEndpointCut false z ∨ B.ambientEndpointTop false z ≤ 0 := by
  exact (T.chains a).first_attachment_union_reflex_germ (T.leftCap a) (T.rightCap a)
    (T.bands a (T.graphs a).firstPiece) ⟨T.length_pos, hr⟩
    (T.cap_disjoint_band_interior _ _ _ _)



theorem last_cap_band_attachment_germ (a : T.decomposition.IncidentEdgeIndex)
    (hr : T.length < 1) :
    let B := T.bands a (T.graphs a).lastPiece
    ∀ᶠ z in 𝓝 (chartAt Plane (T.chart a.1.1 : S)
      (T.decomposition.edgeFromEndpoint a.1.2 true (T.cut a.1.2 true)) +
        T.length • (T.rightCap a).direction),
      z ∈ chartAt Plane (T.chart a.1.1 : S) ''
        (((T.caps (T.decomposition.edgeEndpoint a.1.2 true)).face (T.rightCap a).sector).carrier ∪
          B.faces.carrier) ↔
            0 ≤ B.ambientEndpointCut true z ∨ B.ambientEndpointTop true z ≤ 0 := by
  exact (T.chains a).last_attachment_union_reflex_germ (T.leftCap a) (T.rightCap a)
    (T.bands a (T.graphs a).lastPiece) ⟨T.length_pos, hr⟩
    (T.cap_disjoint_band_interior _ _ _ _)

end RetainedCoordinateTriangulation

end PoincareConjecture.Topology.Surface
