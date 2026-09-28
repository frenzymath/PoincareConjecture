import PoincareConjecture.Proofs.M76.Mathlib.TaperedSegmentDomain










set_option autoImplicit false

open Set Geometry AffineMap

namespace TaperedStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem mem_segmentDomain_iff {q w : E} {β : ℝ} (hβ : 0 < β) {p : E × ℝ} :
    p ∈ segmentDomain q w β ↔ ∃ s ∈ Icc (0 : ℝ) 1,
      p.1 = lineMap q w s ∧ p.2 ∈ Icc 0 (β * s) := by
  rw [← segmentProductCoordinates_image q w hβ]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [PLStrip.segmentProductCoordinates_apply, sub_zero, one_mul, zero_add]
    exact ⟨z.1, hz.1, rfl, hz.2⟩
  · rintro ⟨s, hs, hbase, ht⟩
    refine ⟨(s, p.2), ⟨hs, ht⟩, ?_⟩
    rw [PLStrip.segmentProductCoordinates_apply]
    simp only [sub_zero, one_mul, zero_add]
    exact Prod.ext hbase.symm rfl




theorem segmentDomain_subset_product {q w : E} {β : ℝ} (hβ : 0 < β) :
    segmentDomain q w β ⊆ segment ℝ q w ×ˢ Icc 0 β := by
  intro p hp
  obtain ⟨s, hs, hbase, ht⟩ := (mem_segmentDomain_iff hβ).mp hp
  refine ⟨?_, ht.1, ht.2.trans ?_⟩
  · rw [hbase]
    exact lineMap_mem_segment ℝ q w hs
  · exact mul_le_of_le_one_right hβ.le hs.2



theorem mk_zero_mem_segmentDomain_iff {q w x : E} {β : ℝ} (hβ : 0 < β) :
    (x, 0) ∈ segmentDomain q w β ↔ x ∈ segment ℝ q w := by
  constructor
  · exact fun h => (segmentDomain_subset_product hβ h).1
  · intro hx
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨s, hs, hline⟩ := hx
    exact (mem_segmentDomain_iff hβ).mpr
      ⟨s, hs, hline.symm, le_rfl, mul_nonneg hβ.le hs.1⟩



theorem mk_left_mem_segmentDomain_iff {q w : E} (hqw : q ≠ w)
    {β t : ℝ} (hβ : 0 < β) : (q, t) ∈ segmentDomain q w β ↔ t = 0 := by
  constructor
  · intro hp
    obtain ⟨s, _, hline, ht⟩ := (mem_segmentDomain_iff hβ).mp hp
    have hs : s = 0 := (lineMap_injective ℝ hqw) (by simpa using hline.symm)
    rw [hs, mul_zero] at ht
    exact le_antisymm ht.2 ht.1
  · rintro rfl
    exact (mk_zero_mem_segmentDomain_iff hβ).mpr (left_mem_segment ℝ q w)



theorem mk_right_mem_segmentDomain_iff {q w : E}
    {β t : ℝ} (hβ : 0 < β) : (w, t) ∈ segmentDomain q w β ↔ t ∈ Icc 0 β := by
  constructor
  · intro hp
    exact (segmentDomain_subset_product hβ hp).2
  · intro ht
    apply (mem_segmentDomain_iff hβ).mpr
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, (lineMap_apply_one q w).symm, by simpa using ht⟩




theorem segmentDomain_inter_of_common_left {q w z : E} (hqw : q ≠ w)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hinter : segment ℝ q w ∩ segment ℝ q z = {q}) :
    segmentDomain q w β ∩ segmentDomain q z γ = {(q, 0)} := by
  ext p
  constructor
  · intro hp
    have hbase : p.1 = q := by
      have hmem : p.1 ∈ segment ℝ q w ∩ segment ℝ q z :=
        ⟨(segmentDomain_subset_product hβ hp.1).1, (segmentDomain_subset_product hγ hp.2).1⟩
      rw [hinter] at hmem
      exact hmem
    have hp' : (q, p.2) ∈ segmentDomain q w β := by
      have hpval : p = (q, p.2) := Prod.ext hbase rfl
      exact hpval ▸ hp.1
    exact Prod.ext hbase ((mk_left_mem_segmentDomain_iff hqw hβ).mp hp')
  · rintro rfl
    exact ⟨(mk_zero_mem_segmentDomain_iff hβ).mpr (left_mem_segment ℝ q w),
      (mk_zero_mem_segmentDomain_iff hγ).mpr (left_mem_segment ℝ q z)⟩




theorem segmentDomain_inter_product {q w : E} {B : Set E}
    {β : ℝ} (hβ : 0 < β) (hinter : segment ℝ q w ∩ B = {w}) :
    segmentDomain q w β ∩ (B ×ˢ Icc 0 β) = {w} ×ˢ Icc 0 β := by
  ext p
  constructor
  · intro hp
    have hbase : p.1 = w := by
      have hmem : p.1 ∈ segment ℝ q w ∩ B :=
        ⟨(segmentDomain_subset_product hβ hp.1).1, hp.2.1⟩
      rw [hinter] at hmem
      exact hmem
    exact ⟨hbase, hp.2.2⟩
  · rintro ⟨hb, ht⟩
    have hb' : p.1 = w := hb
    have hwB : w ∈ B := (show w ∈ segment ℝ q w ∩ B from hinter.symm ▸ mem_singleton w).2
    refine ⟨?_, hb'.symm ▸ hwB, ht⟩
    have h := (mk_right_mem_segmentDomain_iff (q := q) (w := w) hβ).mpr ht
    simpa only [← hb'] using h

end TaperedStrip
