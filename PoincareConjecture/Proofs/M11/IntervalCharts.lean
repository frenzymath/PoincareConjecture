import PoincareConjecture.Proofs.M11.IntervalTopology
import PoincareConjecture.Definitions.M11TimeInterval









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

structure IntervalSegmentNeighborhood (I : SpacetimeInterval) where
  left : ℝ
  right : ℝ
  lt : left < right
  segment_subset : Icc left right ⊆ I.domain
  window : Set ℝ
  open_window : IsOpen window
  window_subset : window ∩ I.domain ⊆ Icc left right

theorem exists_intervalSegmentNeighborhood (I : SpacetimeInterval) (t : I.domain) :
    ∃ D : IntervalSegmentNeighborhood I, t.val ∈ D.window := by
  obtain ⟨a, b, hab, _, hsub, hmem⟩ := interval_exists_local_segment I t.property
  obtain ⟨U, hU, htU, hUsub⟩ := mem_nhdsWithin.mp hmem
  exact ⟨⟨a, b, hab, hsub, U, hU, hUsub⟩, htU⟩

namespace IntervalSegmentNeighborhood

variable {I : SpacetimeInterval} (D : IntervalSegmentNeighborhood I)


noncomputable def toSegment : OpenPartialHomeomorph I.domain (Icc D.left D.right) where
  toFun t := projIcc D.left D.right D.lt.le t.val
  invFun t := ⟨t.val, D.segment_subset t.property⟩
  source := {t | t.val ∈ D.window}
  target := {t | t.val ∈ D.window}
  map_source' := by
    intro t ht
    change (projIcc D.left D.right D.lt.le t.val).val ∈ D.window
    rw [projIcc_of_mem D.lt.le (D.window_subset ⟨ht, t.property⟩)]
    exact ht
  map_target' := fun _ ht ↦ ht
  left_inv' := by
    intro t ht
    apply Subtype.ext
    change (projIcc D.left D.right D.lt.le t.val).val = t.val
    rw [projIcc_of_mem D.lt.le (D.window_subset ⟨ht, t.property⟩)]
  right_inv' := by
    intro t _
    exact projIcc_of_mem D.lt.le t.property
  open_source := D.open_window.preimage continuous_subtype_val
  open_target := D.open_window.preimage continuous_subtype_val
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

theorem toSegment_val {t : I.domain} (ht : t.val ∈ D.window) :
    (D.toSegment t).val = t.val := by
  change (projIcc D.left D.right D.lt.le t.val).val = t.val
  rw [projIcc_of_mem D.lt.le (D.window_subset ⟨ht, t.property⟩)]

theorem toSegment_symm_val (t : Icc D.left D.right) :
    (D.toSegment.symm t).val = t.val := rfl

end IntervalSegmentNeighborhood

noncomputable def intervalSegmentAt (I : SpacetimeInterval) (t : I.domain) :
    IntervalSegmentNeighborhood I :=
  Classical.choose (exists_intervalSegmentNeighborhood I t)

theorem intervalSegmentAt_mem (I : SpacetimeInterval) (t : I.domain) :
    t.val ∈ (intervalSegmentAt I t).window :=
  Classical.choose_spec (exists_intervalSegmentNeighborhood I t)


noncomputable def intervalChartAt (I : SpacetimeInterval) (t : I.domain) :
    OpenPartialHomeomorph I.domain (EuclideanHalfSpace 1) :=
  let D := intervalSegmentAt I t
  letI : Fact (D.left < D.right) := ⟨D.lt⟩
  D.toSegment.trans (chartAt (EuclideanHalfSpace 1) (D.toSegment t))

theorem mem_intervalChartAt_source (I : SpacetimeInterval) (t : I.domain) :
    t ∈ (intervalChartAt I t).source := by
  let : Fact ((intervalSegmentAt I t).left < (intervalSegmentAt I t).right) :=
    ⟨(intervalSegmentAt I t).lt⟩
  refine ⟨intervalSegmentAt_mem I t, ?_⟩
  exact mem_chart_source _ _


noncomputable abbrev intervalChartedSpace (I : SpacetimeInterval) :
    ChartedSpace (EuclideanHalfSpace 1) I.domain where
  atlas := Set.range (intervalChartAt I)
  chartAt := intervalChartAt I
  mem_chart_source := mem_intervalChartAt_source I
  chart_mem_atlas := fun t ↦ Set.mem_range_self t


theorem intervalSegment_transition_smooth {I : SpacetimeInterval}
    (D E : IntervalSegmentNeighborhood I) :
    letI : Fact (D.left < D.right) := ⟨D.lt⟩
    letI : Fact (E.left < E.right) := ⟨E.lt⟩
    ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ (E.toSegment ∘ D.toSegment.symm)
      (D.toSegment.target ∩ D.toSegment.symm ⁻¹' E.toSegment.source) := by
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  let : Fact (E.left < E.right) := ⟨E.lt⟩
  apply contMDiffOn_projIcc.comp contMDiff_subtypeVal_Icc.contMDiffOn
  intro t ht
  exact E.window_subset ⟨ht.2, D.segment_subset t.property⟩

theorem intervalChartAt_transition_smooth (I : SpacetimeInterval) (p q : I.domain) :
    ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞
      ((intervalChartAt I p).symm.trans (intervalChartAt I q))
      ((intervalChartAt I p).symm.trans (intervalChartAt I q)).source := by
  let D := intervalSegmentAt I p
  let E := intervalSegmentAt I q
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  let : Fact (E.left < E.right) := ⟨E.lt⟩
  let c := chartAt (EuclideanHalfSpace 1) (D.toSegment p)
  let d := chartAt (EuclideanHalfSpace 1) (E.toSegment q)
  have hc : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hd : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ d d.source := contMDiffOn_chart
  apply (hd.comp' ((intervalSegment_transition_smooth D E).comp' hc)).mono
  dsimp [intervalChartAt, D, E, c, d]
  mfld_set_tac

theorem interval_isManifold (I : SpacetimeInterval) :
    letI := intervalChartedSpace I
    IsManifold (𝓡∂ 1) ∞ I.domain := by
  let := intervalChartedSpace I
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  rw [← contMDiffOn_iff_contDiffOn]
  apply (𝓡∂ 1).contMDiff.comp_contMDiffOn
  exact (intervalChartAt_transition_smooth I p q).comp
    ((𝓡∂ 1).contMDiffOn_symm.mono inter_subset_right) inter_subset_left

theorem interval_inclusion_smooth (I : SpacetimeInterval) :
    letI := intervalChartedSpace I
    ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : I.domain → ℝ) := by
  let := intervalChartedSpace I
  intro t
  let D := intervalSegmentAt I t
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact (contMDiffAt_iff.mp
    (contMDiff_subtypeVal_Icc (n := ∞) (D.toSegment t))).2

theorem interval_boundary_eq (I : SpacetimeInterval) :
    letI := intervalChartedSpace I
    (𝓡∂ 1).boundary I.domain = {t : I.domain | t.val ∈ frontier I.domain} := by
  let := intervalChartedSpace I
  ext t
  let D := intervalSegmentAt I t
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  have hwindow : t.val ∈ D.window := intervalSegmentAt_mem I t
  have htseg : t.val ∈ Icc D.left D.right := D.window_subset ⟨hwindow, t.property⟩
  have hgerm : I.domain =ᶠ[𝓝 t.val] Icc D.left D.right := by
    filter_upwards [D.open_window.mem_nhds hwindow] with s hs
    exact propext ⟨fun h ↦ D.window_subset ⟨hs, h⟩, fun h ↦ D.segment_subset h⟩
  have hfront : t.val ∈ frontier I.domain ↔ t.val ∈ frontier (Icc D.left D.right) := by
    rw [mem_frontier_iff_notMem_interior t.property, mem_frontier_iff_notMem_interior htseg,
      hgerm.mem_interior_iff]
  change (D.toSegment t ∈ (𝓡∂ 1).boundary (Icc D.left D.right)) ↔
    t.val ∈ frontier I.domain
  rw [hfront, boundary_Icc, frontier_Icc D.lt.le]
  simp only [mem_insert_iff, mem_singleton_iff, Subtype.ext_iff,
    D.toSegment_val hwindow, Icc.coe_bot, Icc.coe_top]

end PoincareConjecture.Proofs.M11
