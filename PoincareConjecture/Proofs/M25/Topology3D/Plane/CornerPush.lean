import PoincareConjecture.Proofs.M25.Topology3D.Plane.LineLevel
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OppositeCoordinate
import Mathlib.Analysis.Convex.Hull











set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]


noncomputable def cornerPushPoint (q a b : E) (t : ℝ) : E :=
  AffineMap.lineMap q (midpoint ℝ a b) t


theorem cornerPushPoint_zero (q a b : E) : cornerPushPoint q a b 0 = q := by
  simp [cornerPushPoint]


theorem cornerPushPoint_one (q a b : E) :
    cornerPushPoint q a b 1 = midpoint ℝ a b := by
  simp [cornerPushPoint]



theorem cornerPushPoint_mem_triangle (q a b : E) {t : ℝ} (ht : t ∈ Icc 0 1) :
    cornerPushPoint q a b t ∈ convexHull ℝ {q, a, b} := by
  have hq : q ∈ convexHull ℝ ({q, a, b} : Set E) := subset_convexHull ℝ _ (by simp)
  have hm : midpoint ℝ a b ∈ convexHull ℝ ({q, a, b} : Set E) :=
    segment_subset_convexHull (by simp) (by simp) (midpoint_mem_segment a b)
  exact (convex_convexHull ℝ _).lineMap_mem hq hm ht



theorem cornerPushPoint_simple_corner {q a b : E} (ha : a ≠ q) (hb : b ≠ q)
    (hinter : segment ℝ q a ∩ segment ℝ q b ⊆ {q})
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    cornerPushPoint q a b t ≠ a ∧ cornerPushPoint q a b t ≠ b ∧
      segment ℝ (cornerPushPoint q a b t) a ∩
        segment ℝ (cornerPushPoint q a b t) b = {cornerPushPoint q a b t} := by
  obtain ⟨X, hXa, hXb⟩ := exists_linearMap_neg_pos_of_not_sameRay
    (not_sameRay_sub_of_segments_inter_subset_singleton ha hb hinter)
  have haq : X a < X q := by simpa only [map_sub, sub_neg] using hXa
  have hqb : X q < X b := by simpa only [map_sub, sub_pos] using hXb
  have hmid : X (midpoint ℝ a b) = (X a + X b) / 2 := by
    simp only [midpoint_eq_smul_add, map_smul, map_add, smul_eq_mul, invOf_eq_inv]
    ring
  have hm : X (midpoint ℝ a b) ∈ Ioo (X a) (X b) := by
    rw [hmid]
    constructor <;> linarith
  let v := cornerPushPoint q a b t
  have hv : X v ∈ Ioo (X a) (X b) := by
    have h := (convex_Ioo (X a) (X b)).lineMap_mem ⟨haq, hqb⟩ hm ht
    change X.toAffineMap (AffineMap.lineMap q (midpoint ℝ a b) t) ∈ Ioo (X a) (X b)
    rw [X.toAffineMap.apply_lineMap]
    exact h
  refine ⟨fun h => hv.1.ne (congrArg X h).symm,
    fun h => hv.2.ne (congrArg X h), ?_⟩
  change segment ℝ v a ∩ segment ℝ v b = {v}
  apply subset_antisymm
  · intro z hz
    have hza : X z ∈ X.toAffineMap '' segment ℝ v a := ⟨z, hz.1, rfl⟩
    have hzb : X z ∈ X.toAffineMap '' segment ℝ v b := ⟨z, hz.2, rfl⟩
    rw [image_segment] at hza hzb
    change X z ∈ segment ℝ (X v) (X a) at hza
    change X z ∈ segment ℝ (X v) (X b) at hzb
    rw [segment_symm ℝ (X v) (X a), segment_eq_Icc hv.1.le] at hza
    rw [segment_eq_Icc hv.2.le] at hzb
    have hzv : X z = X v := le_antisymm hza.2 hzb.1
    change z = v
    calc
      z = lineLevelPoint X v a (X z) :=
        (lineLevelPoint_eq_of_mem_segment X hv.1.ne' hz.1).symm
      _ = lineLevelPoint X v a (X v) := congrArg (lineLevelPoint X v a) hzv
      _ = v := lineLevelPoint_left X v a
  · intro z hz
    rw [mem_singleton_iff] at hz
    subst z
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

end Module



theorem contDiff_cornerPushPoint {W E : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℕ∞ω} {q a b : W → E} {tau : W → ℝ}
    (hq : ContDiff ℝ s q) (ha : ContDiff ℝ s a) (hb : ContDiff ℝ s b)
    (htau : ContDiff ℝ s tau) :
    ContDiff ℝ s (fun z => cornerPushPoint (q z) (a z) (b z) (tau z)) := by
  simp only [cornerPushPoint, AffineMap.lineMap_apply_module, midpoint_eq_smul_add]
  exact ((contDiff_const.sub htau).smul hq).add
    (htau.smul (contDiff_const.smul (ha.add hb)))

end PoincareConjecture.M25.Topology3D
