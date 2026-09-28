


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs








set_option autoImplicit false
open Set
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))



theorem exists_edge_graph_neighborhood (e : D.EdgeIndex)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (G : OpenPartialHomeomorph ℝ ℝ) (h : ℝ → ℝ)
    {a b l r : ℝ} (hab : a ≤ b) (hla : l < a) (hbr : b < r)
    (ha : 0 < a) (hb : b < 1) (hGsource : G.source = Ioo l r)
    (hmono : StrictMonoOn G G.source)
    (hgraph_source : ∀ x ∈ G.target, collarParameterEquiv.symm (x, h x) ∈ F.source)
    (hgraph : ∀ t ∈ G.source, (D.edge e.1 e.2).map t =
      F (collarParameterEquiv.symm (G t, h (G t)))) :
    ∃ W : Set M, IsOpen W ∧ (D.edge e.1 e.2).map '' Icc a b ⊆ W ∧
      W ⊆ F.target ∧ ∀ z ∈ W,
        z ∈ chartDiskBoundaryUnion D.centers D.radius ↔
          (collarParameterEquiv (F.symm z)).2 = h (collarParameterEquiv (F.symm z)).1 := by
  classical
  let c := (max l 0 + a) / 2
  let d := (b + min r 1) / 2
  have hc : max l 0 < c ∧ c < a := by
    have h := max_lt hla ha
    dsimp [c]
    constructor <;> linarith
  have hd : b < d ∧ d < min r 1 := by
    have h := lt_min hbr hb
    dsimp [d]
    constructor <;> linarith
  have hcd : c < d := hc.2.trans_le hab |>.trans hd.1
  have hc0 : 0 < c := (le_max_right l 0).trans_lt hc.1
  have hd1 : d < 1 := hd.2.trans_le (min_le_right r 1)
  have hJ : Icc c d ⊆ G.source := by
    rw [hGsource]
    exact fun t ht => ⟨(le_max_left l 0).trans_lt (hc.1.trans_le ht.1),
      ht.2.trans_lt (hd.2.trans_le (min_le_left r 1))⟩
  have hI : Icc a b ⊆ Ioo c d := fun t ht =>
    ⟨hc.2.trans_le ht.1, ht.2.trans_lt hd.1⟩
  have hcoords (t : ℝ) (ht : t ∈ G.source) :
      collarParameterEquiv (F.symm ((D.edge e.1 e.2).map t)) = (G t, h (G t)) := by
    rw [hgraph t ht, F.left_inv (hgraph_source _ (G.map_source ht)),
      collarParameterEquiv.apply_symm_apply]
  let T : Set M :=
    (⋃ j : {j : D.EdgeIndex // j ≠ e}, (D.edge j.1.1 j.1.2).map '' Icc (0 : ℝ) 1) ∪
      (D.edge e.1 e.2).map '' (Icc 0 c ∪ Icc d 1)
  have hT : IsClosed T := (isClosed_iUnion_of_finite (fun j : {j : D.EdgeIndex // j ≠ e} =>
    (D.isCompact_edge j.1).isClosed)).union
      (((isCompact_Icc.union isCompact_Icc).image (D.edge_contMDiff e).continuous).isClosed)
  let xcoord : M → ℝ := fun z => (collarParameterEquiv (F.symm z)).1
  let V : Set M := F.target ∩ xcoord ⁻¹' Ioo (G c) (G d)
  have hV : IsOpen V :=
    (collarParameterEquiv.continuous.comp_continuousOn F.continuousOn_symm).fst.isOpen_inter_preimage
      F.open_target isOpen_Ioo
  let W := V \ T
  have hW : IsOpen W := hV.inter hT.isOpen_compl
  have havoid (t : ℝ) (ht : t ∈ Icc a b) : (D.edge e.1 e.2).map t ∉ T := by
    have htcd := hI ht
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
    rintro (hother | htail)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hother
      have hdis := Poincare.Topology.disjoint_arc_interior_of_endpoint_intersections
        (D.edge_injective e.1 e.2) (fun z hz => (D.edge_intersection e j (Ne.symm j.2) hz).1)
      exact disjoint_left.mp hdis ⟨t, ht01, rfl⟩ hj
    · obtain ⟨s, hs, heq⟩ := htail
      have hs01 : s ∈ Icc (0 : ℝ) 1 := by
        rcases hs with hs | hs
        · exact ⟨hs.1, hs.2.trans (hcd.le.trans hd1.le)⟩
        · exact ⟨(hc0.le.trans hcd.le).trans hs.1, hs.2⟩
      have hst := D.edge_injective e.1 e.2 hs01 (Ioo_subset_Icc_self ht01) heq
      subst s
      exact hs.elim (fun hs => (not_le_of_gt htcd.1) hs.2)
        (fun hs => (not_le_of_gt htcd.2) hs.1)
  refine ⟨W, hW, ?_, fun z hz => hz.1.1, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    have htG := hJ (Ioo_subset_Icc_self (hI ht))
    refine ⟨⟨?_, ?_⟩, havoid t ht⟩
    · rw [hgraph t htG]
      exact F.map_source (hgraph_source _ (G.map_source htG))
    · change G c < xcoord ((D.edge e.1 e.2).map t) ∧
        xcoord ((D.edge e.1 e.2).map t) < G d
      dsimp only [xcoord]
      rw [hcoords t htG]
      exact ⟨hmono (hJ (left_mem_Icc.mpr hcd.le)) htG (hI ht).1,
        hmono htG (hJ (right_mem_Icc.mpr hcd.le)) (hI ht).2⟩
  · intro z hz
    constructor
    · intro hzK
      rw [← D.boundary_cover] at hzK
      obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.mp hzK
      have hje : j = e := by
        by_contra hj
        exact hz.2 (Or.inl (mem_iUnion.mpr ⟨⟨j, hj⟩, t, ht, rfl⟩))
      subst j
      have htcd : t ∈ Ioo c d := by
        constructor
        · by_contra h
          exact hz.2 (Or.inr ⟨t, Or.inl ⟨ht.1, le_of_not_gt h⟩, rfl⟩)
        · by_contra h
          exact hz.2 (Or.inr ⟨t, Or.inr ⟨le_of_not_gt h, ht.2⟩, rfl⟩)
      rw [hcoords t (hJ (Ioo_subset_Icc_self htcd))]
    · intro hzgraph
      have himage : G '' Icc c d = Icc (G c) (G d) :=
        (G.continuousOn.mono hJ).image_Icc_of_monotoneOn hcd.le (hmono.monotoneOn.mono hJ)
      have hx : xcoord z ∈ G '' Icc c d := by
        rw [himage]
        exact Ioo_subset_Icc_self hz.1.2
      obtain ⟨t, ht, heq⟩ := hx
      have hzt : z = (D.edge e.1 e.2).map t := by
        rw [hgraph t (hJ ht), heq]
        have hcoord : (xcoord z, h (xcoord z)) = collarParameterEquiv (F.symm z) := by
          exact Prod.ext rfl hzgraph.symm
        rw [hcoord, collarParameterEquiv.symm_apply_apply, F.right_inv hz.1.1]
      rw [hzt, ← D.boundary_cover]
      exact mem_iUnion.mpr ⟨e, t, ⟨hc0.le.trans ht.1, ht.2.trans hd1.le⟩, rfl⟩



theorem exists_edge_graph_tube (e : D.EdgeIndex)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (G : OpenPartialHomeomorph ℝ ℝ) (h : ℝ → ℝ)
    {a b l r : ℝ} (hab : a ≤ b) (hla : l < a) (hbr : b < r)
    (ha : 0 < a) (hb : b < 1) (hGsource : G.source = Ioo l r)
    (hmono : StrictMonoOn G G.source) (hh : ContinuousOn h G.target)
    (hgraph_source : ∀ x ∈ G.target, collarParameterEquiv.symm (x, h x) ∈ F.source)
    (hgraph : ∀ t ∈ G.source, (D.edge e.1 e.2).map t =
      F (collarParameterEquiv.symm (G t, h (G t)))) :
    ∃ (X : Set ℝ) (δ : ℝ), IsOpen X ∧ Icc (G a) (G b) ⊆ X ∧ X ⊆ G.target ∧
      0 < δ ∧ ∀ x ∈ X, ∀ z : ℝ, |z| < δ →
        collarParameterEquiv.symm (x, h x + z) ∈ F.source ∧
        (F (collarParameterEquiv.symm (x, h x + z)) ∈
          chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) := by
  obtain ⟨W, hW, harc, hWF, hboundary⟩ :=
    D.exists_edge_graph_neighborhood e F G h hab hla hbr ha hb hGsource hmono hgraph_source hgraph
  have hI : Icc a b ⊆ G.source := by
    rw [hGsource]
    exact fun t ht => ⟨hla.trans_le ht.1, ht.2.trans_lt hbr⟩
  have himage : G '' Icc a b = Icc (G a) (G b) :=
    (G.continuousOn.mono hI).image_Icc_of_monotoneOn hab (hmono.monotoneOn.mono hI)
  let lift : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun q => collarParameterEquiv.symm (q.1, h q.1 + q.2)
  let S := F.source ∩ F ⁻¹' W
  have hS : IsOpen S := F.continuousOn.isOpen_inter_preimage F.open_source hW
  have hlift : ContinuousOn lift {q | q.1 ∈ G.target} :=
    collarParameterEquiv.symm.continuous.comp_continuousOn
      (continuousOn_fst.prodMk ((hh.comp continuousOn_fst (fun _ hq => hq)).add continuousOn_snd))
  let V : Set (ℝ × ℝ) := {q | q.1 ∈ G.target} ∩ lift ⁻¹' S
  have hV : IsOpen V := hlift.isOpen_inter_preimage
    (G.open_target.preimage continuous_fst) hS
  have haxis : Icc (G a) (G b) ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [← himage] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have htG := G.map_source (hI ht)
    refine ⟨htG, ?_⟩
    change collarParameterEquiv.symm (G t, h (G t) + 0) ∈ S
    simp only [add_zero]
    refine ⟨hgraph_source _ htG, ?_⟩
    change F (collarParameterEquiv.symm (G t, h (G t))) ∈ W
    rw [← hgraph t (hI ht)]
    exact harc ⟨t, ht, rfl⟩
  obtain ⟨U, Z, hU, hZ, hIU, h0Z, hUZ⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hV haxis
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hZ.mem_nhds (h0Z (mem_singleton (0 : ℝ))))
  refine ⟨U ∩ G.target, δ, hU.inter G.open_target, ?_, inter_subset_right, hδ, ?_⟩
  · intro x hx
    refine ⟨hIU hx, ?_⟩
    rw [← himage] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact G.map_source (hI ht)
  · intro x hx z hz
    have hloc := hUZ (a := (x, z)) ⟨hx.1, hball (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz)⟩
    have hs := hloc.2.1
    refine ⟨hs, ?_⟩
    rw [hboundary _ hloc.2.2, F.left_inv hs, collarParameterEquiv.apply_symm_apply]
    simp

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
