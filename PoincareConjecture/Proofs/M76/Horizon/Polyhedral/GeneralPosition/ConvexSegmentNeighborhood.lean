import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening









set_option autoImplicit false

open Set Metric

theorem exists_convex_segment_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} {W : Set E} (hW : IsOpen W) (hab : segment ℝ a b ⊆ W) :
    ∃ (δ : ℝ) (V : Set E), 0 < δ ∧ IsOpen V ∧ Convex ℝ V ∧
      segment ℝ a b ⊆ V ∧ V ⊆ W ∧ ball a δ ⊆ V ∧ ball b δ ⊆ V := by
  have hc : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨δ, hδ, hsub⟩ := hc.exists_thickening_subset_open hW hab
  refine ⟨δ, thickening δ (segment ℝ a b), hδ, isOpen_thickening,
    (convex_segment a b).thickening δ, self_subset_thickening hδ _, hsub, ?_, ?_⟩
  · intro x hx
    exact mem_thickening_iff.mpr ⟨a, left_mem_segment ℝ a b, hx⟩
  · intro x hx
    exact mem_thickening_iff.mpr ⟨b, right_mem_segment ℝ a b, hx⟩
