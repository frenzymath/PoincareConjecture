import PoincareConjecture.Proofs.M76.Mathlib.TriangleZeroSlice
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlice
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Affine.AddTorsor











set_option autoImplicit false
open Set

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem openSegment_notMem_affineSubspace
    (P : AffineSubspace ℝ E) {u w x : E} (hu : u ∈ P) (hw : w ∉ P)
    (hx : x ∈ openSegment ℝ u w) : x ∉ P := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  intro hxP
  have h := P.smul_vsub_vadd_mem t⁻¹ hxP hu hu
  apply hw
  simpa only [lineMap_apply_module', vsub_eq_sub, vadd_eq_add, add_sub_cancel_right,
    smul_smul, inv_mul_cancel₀ ht.1.ne', one_smul, sub_add_cancel] using h



theorem exists_triangle_edge_zero_segment (A : E →ᵃ[ℝ] ℝ) {u v w : E}
    (hu : A u < 0) (hv : 0 < A v) (hw : w ∉ affineSpan ℝ ({u, v} : Set E)) :
    ∃ z : E, z ≠ A.zeroCrossing u v ∧
      convexHull ℝ (insert w ({u, v} : Set E)) ∩ {x | A x = 0} =
        segment ℝ (A.zeroCrossing u v) z := by
  have hy : A.zeroCrossing u v ∈ affineSpan ℝ ({u, v} : Set E) :=
    lineMap_mem_affineSpan_pair _ _ _
  rcases lt_trichotomy (A w) 0 with hwn | hwz | hwp
  · let z := A.zeroCrossing w v
    have hz : z ∉ affineSpan ℝ ({u, v} : Set E) := by
      apply openSegment_notMem_affineSubspace _ (right_mem_affineSpan_pair ℝ u v) hw
      rw [openSegment_symm]
      exact A.zeroCrossing_mem_openSegment hwn hv
    refine ⟨z, (fun h => hz (h.symm ▸ hy)), ?_⟩
    have hset : insert w ({u, v} : Set E) = insert v {u, w} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rw [hset]
    exact A.convexHull_insert_pair_inter_zero hu hwn hv
  · refine ⟨w, (fun h => hw (h.symm ▸ hy)), ?_⟩
    rw [A.convexHull_zero_apex_pair_inter_zero hwz hu hv, segment_symm]
  · let z := (-A).zeroCrossing w u
    have hz : z ∉ affineSpan ℝ ({u, v} : Set E) := by
      apply openSegment_notMem_affineSubspace _ (left_mem_affineSpan_pair ℝ u v) hw
      rw [openSegment_symm]
      exact (-A).zeroCrossing_mem_openSegment (neg_neg_of_pos hwp) (neg_pos.mpr hu)
    have hy' : (-A).zeroCrossing v u = A.zeroCrossing u v := by
      apply A.eq_zeroCrossing_of_mem_affineSpan (hu.trans hv).ne
      · rw [pair_comm]
        exact lineMap_mem_affineSpan_pair _ _ _
      · have hzero := (-A).zeroCrossing_apply
          (ne_of_lt ((neg_neg_of_pos hv).trans (neg_pos.mpr hu)))
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hzero
    refine ⟨z, (fun h => hz (h.symm ▸ hy)), ?_⟩
    have hset : insert w ({u, v} : Set E) = insert u {v, w} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    have hslice := (-A).convexHull_insert_pair_inter_zero
      (neg_neg_of_pos hv) (neg_neg_of_pos hwp) (neg_pos.mpr hu)
    rw [hy'] at hslice
    simpa only [hset, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hslice



theorem exists_triangle_edge_halfInterval (A : E →ᵃ[ℝ] ℝ) {u v w : E}
    (hu : A u < 0) (hv : 0 < A v) (hw : w ∉ affineSpan ℝ ({u, v} : Set E))
    {U : Set E} (hU : IsOpen U) (hyU : A.zeroCrossing u v ∈ U) :
    let y := A.zeroCrossing u v
    ∃ (z : E) (r : ℝ), z ≠ y ∧ 0 < r ∧ r < dist y z ∧ Metric.ball y r ⊆ U ∧
      (convexHull ℝ (insert w ({u, v} : Set E)) ∩ {x | A x = 0}) ∩ Metric.ball y r =
        lineMap y z '' Ico (0 : ℝ) (r / dist y z) ∧
      Topology.IsEmbedding (lineMap y z : ℝ → E) ∧
      ∀ t ∈ Ico (0 : ℝ) (r / dist y z),
        lineMap y z t ∈ segment ℝ u v ↔ t = 0 := by
  obtain ⟨z, hzy, hslice⟩ := A.exists_triangle_edge_zero_segment hu hv hw
  let y := A.zeroCrossing u v
  have hdist : 0 < dist y z := dist_pos.mpr hzy.symm
  obtain ⟨delta, hdelta, hdeltaU⟩ := Metric.isOpen_iff.mp hU y hyU
  let r := min delta (dist y z / 2)
  have hr : 0 < r := lt_min hdelta (half_pos hdist)
  have hrlt : r < dist y z := (min_le_right _ _).trans_lt (half_lt_self hdist)
  have hfrac : r / dist y z < 1 := (div_lt_one hdist).mpr hrlt
  have hlocal : segment ℝ y z ∩ Metric.ball y r =
      lineMap y z '' Ico (0 : ℝ) (r / dist y z) := by
    ext x
    constructor
    · rintro ⟨hx, hxball⟩
      rw [segment_eq_image_lineMap] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      refine ⟨t, ⟨ht.1, ?_⟩, rfl⟩
      apply (lt_div_iff₀ hdist).mpr
      simpa only [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs,
        abs_of_nonneg ht.1] using hxball
    · rintro ⟨t, ht, rfl⟩
      refine ⟨lineMap_mem_segment ℝ y z ⟨ht.1, (ht.2.trans hfrac).le⟩, ?_⟩
      rw [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (lt_div_iff₀ hdist).mp ht.2
  refine ⟨z, r, hzy, hr, hrlt, (Metric.ball_subset_ball (min_le_left _ _)).trans hdeltaU,
    hslice ▸ hlocal, (antilipschitzWith_lineMap hzy.symm).isEmbedding
      (lipschitzWith_lineMap y z).continuous, ?_⟩
  intro t ht
  have hxsection : lineMap y z t ∈
      convexHull ℝ (insert w ({u, v} : Set E)) ∩ {x | A x = 0} := by
    rw [hslice]
    exact lineMap_mem_segment ℝ y z ⟨ht.1, (ht.2.trans hfrac).le⟩
  constructor
  · intro hxe
    have hxy : lineMap y z t = y := by
      have hmem : lineMap y z t ∈ convexHull ℝ ({u, v} : Set E) ∩ {x | A x = 0} :=
        ⟨by simpa only [convexHull_pair] using hxe, hxsection.2⟩
      simpa only [A.convexHull_pair_inter_zero hu hv, mem_singleton_iff] using hmem
    exact lineMap_injective ℝ hzy.symm (hxy.trans (lineMap_apply_zero y z).symm)
  · rintro rfl
    rw [lineMap_apply_zero]
    exact openSegment_subset_segment ℝ u v (A.zeroCrossing_mem_openSegment hu hv)

end AffineMap
