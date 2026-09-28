


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapWidths
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Interfaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Intersections









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)}

namespace CapGraphEndpoint

variable
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → M}
  {B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions} {a b trim : ℝ} {terminal : Bool}
  {g : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b}
  (E : D.CapGraphEndpoint P region chart B e R g terminal trim)


def chordSegment (r : ℝ) : Set M :=
  (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) +
      u • E.direction)) '' Icc (0 : ℝ) r

theorem chordSegment_subset_cap {r : ℝ} (hr : r ≤ 1) :
    E.chordSegment r ⊆ ((B (D.edgeEndpoint e terminal)).face E.sector).carrier := by
  rintro q ⟨u, hu, rfl⟩
  dsimp only
  rw [E.chord_map]
  apply ((B (D.edgeEndpoint e terminal)).face E.sector).isClosed_carrier.frontier_subset
  apply ((B (D.edgeEndpoint e terminal)).face E.sector).boundary_image_subset_frontier 0
  refine ⟨if E.radialEdge = 1 then 1 - u else u, ?_, rfl⟩
  split_ifs <;> constructor <;> linarith [hu.1, hu.2]

theorem chordSegment_subset_region_caps {r : ℝ} (hr : r ≤ 1) :
    E.chordSegment r ⊆ D.vertexCapsInRegion B region R := by
  intro q hq
  exact mem_iUnion.mpr
    ⟨⟨(D.edgeEndpoint e terminal, E.sector), E.sector_region⟩,
      E.chordSegment_subset_cap hr hq⟩

end CapGraphEndpoint

namespace OrientedGraphPiece.FixedStripBandFaces

variable
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → M}
  {B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions} {a b δ ra rb ua wa ub wb : ℝ}
  {g : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b}
  {Q : Poincare.Topology.Plane.Curves.TransverseGraphCuts g.lower
    (g.parameter a) (g.parameter b) ua wa ub wb}
  (F : g.FixedStripBandFaces Q δ ra rb)

omit [T2Space M] in
theorem leftCut_subset_carrier : F.faces.leftCut ⊆ F.faces.carrier := by
  intro q hq
  rw [← F.faces.left_height_image] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  dsimp only
  rw [F.coordinates_eq, F.carrier_eq_fixed_strip]
  exact ⟨(0, z), ⟨by simp, hz⟩, rfl⟩

omit [T2Space M] in
theorem rightCut_subset_carrier : F.faces.rightCut ⊆ F.faces.carrier := by
  intro q hq
  rw [← F.faces.right_height_image] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  dsimp only
  rw [F.coordinates_eq, F.carrier_eq_fixed_strip]
  exact ⟨(1, z), ⟨by simp, hz⟩, rfl⟩

omit [T2Space M] in


theorem inter_region_caps_subset_cuts
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
      Q.coordinates g.parameter.open_target g.lower_smooth (t, z) ∉
        D.graphCapObstacle region chart B R g.frame) :
    F.faces.carrier ∩ D.vertexCapsInRegion B region R ⊆ F.faces.leftCut ∪ F.faces.rightCut := by
  rintro q ⟨hq, hqcap⟩
  rw [F.carrier_eq_fixed_strip] at hq
  obtain ⟨⟨t, z⟩, ⟨ht, hz, hheight⟩, rfl⟩ := hq
  by_cases ht0 : t = 0
  · subst t
    left
    rw [← F.faces.left_height_image]
    exact ⟨z, ⟨hz, hheight⟩, F.coordinates_eq (0, z)⟩
  by_cases ht1 : t = 1
  · subst t
    right
    rw [← F.faces.right_height_image]
    exact ⟨z, ⟨hz, hheight⟩, F.coordinates_eq (1, z)⟩
  have htopen : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have hzδ : |z| < δ := by
    rw [abs_of_nonneg hz]
    exact hheight.trans_lt (F.height_bounds ht).2
  apply False.elim
  apply havoid t htopen z hzδ
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
  have hsource := (F.subgraph_subset_source ⟨ht, hz, hheight⟩).2
  change g.frame.symm (Q.coordinates g.parameter.open_target g.lower_smooth (t, z)) ∈ c.target at hsource
  have heq : c (g.strip Q (t, z)) =
      g.frame.symm (Q.coordinates g.parameter.open_target g.lower_smooth (t, z)) := c.right_inv hsource
  refine ⟨c (g.strip Q (t, z)), ⟨g.strip Q (t, z), hqcap, rfl⟩, ?_⟩
  rw [heq, g.frame.apply_symm_apply]

end OrientedGraphPiece.FixedStripBandFaces

section InternalRays

variable
  (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
  (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
  (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s)))
  (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
  (hlocal : ∀ p q, q ∈ (P p).carrier →
    (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
  (cut : D.EdgeIndex → Bool → ℝ)
  (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3))
  (hmatch : ∀ a b, ∃ d : Bool × Bool,
    (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
      D.edgeFromEndpoint a b '' Icc 0 (cut a b))

include hdisjoint hlocal hcut hmatch



theorem exists_internal_cap_free_ray (e : D.EdgeIndex) (R : D.regions)
    {t : ℝ} (ht : t ∈ Ioo (cut e false) (1 - cut e true))
    (hchart : (D.edge e.1 e.2).map t ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source)
    (d : EuclideanSpace ℝ (Fin 2)) :
    ∃ ε > 0, ∀ u ∈ Icc (0 : ℝ) ε,
      chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map t) + u • d ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).target ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map t) + u • d) ∉
          D.vertexCapsInRegion B region R := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
  let f : ℝ → EuclideanSpace ℝ (Fin 2) := fun u => c ((D.edge e.1 e.2).map t) + u • d
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf0 : f 0 ∈ c.target := by simpa [f] using c.map_source hchart
  have hnot : (D.edge e.1 e.2).map t ∉ D.vertexCapsInRegion B region R := by
    intro hq
    exact disjoint_left.mp
      (D.vertex_caps_disjoint_open_middleArc P B hdisjoint hlocal cut hcut hmatch e)
      (D.vertexCapsInRegion_subset_union B region R hq) ⟨t, ht, rfl⟩
  have hzero : c.symm (f 0) = (D.edge e.1 e.2).map t := by
    simpa [f] using c.left_inv hchart
  have hpath : ContinuousAt (c.symm ∘ f) 0 :=
    (c.symm.continuousAt hf0).comp hf.continuousAt
  have hsource : ∀ᶠ u in 𝓝 (0 : ℝ), f u ∈ c.target :=
    hf.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds hf0)
  have havoid : ∀ᶠ u in 𝓝 (0 : ℝ), c.symm (f u) ∉ D.vertexCapsInRegion B region R :=
    hpath.preimage_mem_nhds ((D.isClosed_vertexCapsInRegion B region R).isOpen_compl.mem_nhds
      (show (c.symm ∘ f) 0 ∉ D.vertexCapsInRegion B region R by simpa [hzero] using hnot))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hsource.and havoid)
  refine ⟨ρ / 2, half_pos hρ, fun u hu => hball ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hu.1] using
    hu.2.trans_lt (half_lt_self hρ)

namespace OrientedEdgeGraphSubdivision

variable {e : D.EdgeIndex} {R : D.regions}
  {S : D.OrientedEdgeGraphSubdivision e R
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut e false) (1 - cut e true)}
  {dLeft dRight : EuclideanSpace ℝ (Fin 2)} (K : S.CutChain dLeft dRight)



theorem CutChain.exists_internal_cap_free_length (j : Fin (S.count + 1))
    (hj0 : j ≠ 0) (hjlast : j ≠ Fin.last S.count) :
    ∃ ε > 0, ∀ u ∈ Icc (0 : ℝ) ε,
      chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map (S.cut j)) +
          u • K.direction j ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).target ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map (S.cut j)) +
          u • K.direction j) ∉ D.vertexCapsInRegion B region R := by
  have hjpos : 0 < j := lt_of_le_of_ne (Fin.zero_le j) (Ne.symm hj0)
  have hjlt : j < Fin.last S.count := lt_of_le_of_ne (Fin.le_last j) hjlast
  let i : Fin S.count := ⟨j.val, hjlt⟩
  have hij : i.castSucc = j := Fin.ext rfl
  have ht : S.cut j ∈ Ioo (cut e false) (1 - cut e true) := by
    constructor
    · simpa only [S.cut_first] using S.cut_strictMono hjpos
    · simpa only [S.cut_last] using S.cut_strictMono hjlt
  have hs := (S.piece i).source_chart ((S.piece i).interval_source ⟨le_rfl, (S.cut_lt i).le⟩)
  rw [hij] at hs
  exact exists_internal_cap_free_ray P region chart B hdisjoint hlocal cut hcut hmatch e R
    ht hs (K.direction j)



theorem CutChain.exists_all_internal_cap_free_length :
    ∃ ε > 0, ∀ j : Fin (S.count + 1), j ≠ 0 → j ≠ Fin.last S.count →
      ∀ u ∈ Icc (0 : ℝ) ε,
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
          (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map (S.cut j)) +
            u • K.direction j) ∉ D.vertexCapsInRegion B region R := by
  classical
  have hex (j : Fin (S.count + 1)) : ∃ ε > 0,
      j ≠ 0 → j ≠ Fin.last S.count → ∀ u ∈ Icc (0 : ℝ) ε,
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
          (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map (S.cut j)) +
            u • K.direction j) ∉ D.vertexCapsInRegion B region R := by
    by_cases hj0 : j = 0
    · exact ⟨1, zero_lt_one, fun h => False.elim (h hj0)⟩
    by_cases hjlast : j = Fin.last S.count
    · exact ⟨1, zero_lt_one, fun _ h => False.elim (h hjlast)⟩
    obtain ⟨ε, hε, hfree⟩ := K.exists_internal_cap_free_length P region chart B hdisjoint hlocal
      cut hcut hmatch j hj0 hjlast
    exact ⟨ε, hε, fun _ _ u hu => (hfree u hu).2⟩
  choose ε hε hfree using hex
  let ρ := Finset.univ.inf' Finset.univ_nonempty ε
  have hρ : 0 < ρ := by simpa [ρ] using hε
  refine ⟨ρ, hρ, fun j hj0 hjlast u hu => hfree j hj0 hjlast u ?_⟩
  exact ⟨hu.1, hu.2.trans (Finset.inf'_le ε (Finset.mem_univ j))⟩

end OrientedEdgeGraphSubdivision
end InternalRays

namespace OrientedEdgeGraphSubdivision

section Attachments

variable
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → M}
  {B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {cut : D.EdgeIndex → Bool → ℝ} {e : D.EdgeIndex} {R : D.regions}
  {S : D.OrientedEdgeGraphSubdivision e R
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut e false) (1 - cut e true)}
  (L : D.CapGraphEndpoint P region chart B e R (S.piece S.firstPiece) false (cut e false))
  (T : D.CapGraphEndpoint P region chart B e R (S.piece S.lastPiece) true (cut e true))
  (K : S.CutChain L.direction T.direction)



theorem CutChain.band_inter_region_caps {r δ : ℝ} (hr : r ≤ 1)
    (hfree : ∀ j : Fin (S.count + 1), j ≠ 0 → j ≠ Fin.last S.count →
      ∀ u ∈ Icc (0 : ℝ) r,
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
          (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map (S.cut j)) +
            u • K.direction j) ∉ D.vertexCapsInRegion B region R)
    (i : Fin S.count) (F : (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
      (K.graphCuts i).coordinates (S.piece i).parameter.open_target
        (S.piece i).lower_smooth (t, z) ∉ D.graphCapObstacle region chart B R (S.piece i).frame) :
    F.faces.carrier ∩ D.vertexCapsInRegion B region R =
      (if i = S.firstPiece then L.chordSegment r else ∅) ∪
        (if i = S.lastPiece then T.chordSegment r else ∅) := by
  have hleftRay : F.faces.leftCut =
      (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map (S.cut i.castSucc)) +
          u • K.direction i.castSucc)) '' Icc (0 : ℝ) r := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
      OpenPartialHomeomorph.symm_symm] using F.leftCut_eq_ray (S.cut_lt i).le
  have hrightRay : F.faces.rightCut =
      (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map (S.cut i.succ)) +
          u • K.direction i.succ)) '' Icc (0 : ℝ) r := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
      OpenPartialHomeomorph.symm_symm] using F.rightCut_eq_ray (S.cut_lt i).le
  have hleft : F.faces.leftCut ∩ D.vertexCapsInRegion B region R =
      if i = S.firstPiece then L.chordSegment r else ∅ := by
    by_cases hi : i = S.firstPiece
    · subst i
      have heq : F.faces.leftCut = L.chordSegment r := by
        simpa only [S.firstPiece_castSucc, S.cut_first, K.first, CapGraphEndpoint.chordSegment,
          edgeFromEndpoint, Bool.false_eq_true, ite_false] using hleftRay
      rw [heq, if_pos rfl, inter_eq_left.mpr (L.chordSegment_subset_region_caps hr)]
    · rw [if_neg hi, hleftRay]
      apply eq_empty_iff_forall_notMem.mpr
      rintro q ⟨⟨u, hu, rfl⟩, hq⟩
      have hj0 : i.castSucc ≠ 0 := by
        intro he
        have hv : i.val = 0 := congrArg (fun j : Fin (S.count + 1) => j.val) he
        exact hi (Fin.ext hv)
      exact hfree i.castSucc hj0 (ne_of_lt (Fin.castSucc_lt_last i)) u hu hq
  have hright : F.faces.rightCut ∩ D.vertexCapsInRegion B region R =
      if i = S.lastPiece then T.chordSegment r else ∅ := by
    by_cases hi : i = S.lastPiece
    · subst i
      have heq : F.faces.rightCut = T.chordSegment r := by
        simpa only [S.lastPiece_succ, S.cut_last, K.last, CapGraphEndpoint.chordSegment,
          edgeFromEndpoint, ite_true] using hrightRay
      rw [heq, if_pos rfl, inter_eq_left.mpr (T.chordSegment_subset_region_caps hr)]
    · rw [if_neg hi, hrightRay]
      apply eq_empty_iff_forall_notMem.mpr
      rintro q ⟨⟨u, hu, rfl⟩, hq⟩
      have hj0 : i.succ ≠ 0 := by intro he; have hv := congrArg Fin.val he; simp at hv
      have hjlast : i.succ ≠ Fin.last S.count := by
        intro he
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val he
        change i.val + 1 = S.count at hv
        change i.val = S.count - 1
        omega
      exact hfree i.succ hj0 hjlast u hu hq
  calc
    F.faces.carrier ∩ D.vertexCapsInRegion B region R =
        (F.faces.leftCut ∪ F.faces.rightCut) ∩ D.vertexCapsInRegion B region R := by
      apply subset_antisymm
      · intro q hq
        exact ⟨F.inter_region_caps_subset_cuts havoid hq, hq.2⟩
      · rintro q ⟨hq | hq, hqcap⟩
        · exact ⟨F.leftCut_subset_carrier hq, hqcap⟩
        · exact ⟨F.rightCut_subset_carrier hq, hqcap⟩
    _ = _ := by rw [union_inter_distrib_right, hleft, hright]

end Attachments
end OrientedEdgeGraphSubdivision

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
