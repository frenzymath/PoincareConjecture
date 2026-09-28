import PoincareConjecture.Proofs.M76.Mathlib.ZeroApexSlice
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevel









set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]




theorem convexHull_insert_level_homothety (A : E →ᵃ[ℝ] ℝ)
    {q : E} (hq : A q = 0) {s : Set E} (hs : s.Nonempty)
    {β c : ℝ} (hβ : 0 < β) (hAs : ∀ x ∈ s, A x = β) (hc : c ∈ Icc 0 β) :
    convexHull ℝ (insert q s) ∩ {x | A x = c} =
      homothety q (c / β) '' convexHull ℝ s := by
  have hbase (y : E) (hy : y ∈ convexHull ℝ s) : A y = β :=
    convexHull_min hAs ((convex_singleton β).affine_preimage A) hy
  ext x
  constructor
  · rintro ⟨hx, hAx⟩
    rw [convexHull_insert hs] at hx
    obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hx
    have haq : a = q := mem_singleton_iff.mp ha
    subst a
    rw [segment_eq_image_lineMap] at hxy
    obtain ⟨t, _, rfl⟩ := hxy
    change A (lineMap q y t) = c at hAx
    have ht : t = c / β := (eq_div_iff hβ.ne').mpr (by
      simpa only [A.apply_lineMap, hq, hbase y hy, lineMap_apply_ring', sub_zero, add_zero]
        using hAx)
    exact ⟨y, hy, by rw [homothety_eq_lineMap, ← ht]⟩
  · rintro ⟨y, hy, rfl⟩
    rw [homothety_eq_lineMap]
    refine ⟨(convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (mem_insert _ _))
      (convexHull_mono (subset_insert q s) hy)
      (lineMap_mem_segment ℝ q y
        ⟨div_nonneg hc.1 hβ.le, (div_le_one hβ).mpr hc.2⟩), ?_⟩
    change A (lineMap q y (c / β)) = c
    rw [A.apply_lineMap, hq, hbase y hy, lineMap_apply_ring', sub_zero, add_zero,
      div_mul_cancel₀ c hβ.ne']




theorem zeroApex_residual_level_homothety (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hq : A q = 0) (hw : A w = 0) {β c : ℝ} (hβ : 0 < β) (hβv : β < A v)
    (hc : c ∈ Icc 0 β) :
    convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) ∩
        {x | A x = c} =
      homothety q (c / β) '' segment ℝ (A.edgeLevel w v β) (A.edgeLevel q v β) := by
  rw [← convexHull_pair]
  apply A.convexHull_insert_level_homothety hq (by simp) hβ _ hc
  intro x hx
  rcases hx with rfl | rfl
  · exact A.apply_edgeLevel (by rw [hw]; exact (hβ.trans hβv).ne') β
  · exact A.apply_edgeLevel (by rw [hq]; exact (hβ.trans hβv).ne') β





theorem homothety_zero_edgeLevel (A : E →ᵃ[ℝ] ℝ) {q : E} (hq : A q = 0)
    {β : ℝ} (hβ : β ≠ 0) (u : E) (c : ℝ) :
    homothety q (c / β) (A.edgeLevel q u β) = A.edgeLevel q u c := by
  rw [homothety_eq_lineMap, lineMap_apply_module', edgeLevel, edgeLevel, hq, sub_zero,
    sub_zero, add_sub_cancel_right, smul_smul, div_mul_cancel₀ c hβ]





theorem positive_triangle_level_homothety (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) {β c : ℝ} (hβ : 0 < β) (hβu : β < A u) (hβv : β < A v)
    (hc : c ∈ Ioc 0 β) :
    convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = c} =
      homothety q (c / β) ''
        (convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = β}) := by
  rw [A.triangle_section_eq_edgeLevels (by rw [hq]; exact hc.1)
      (hc.2.trans_lt hβu) (hc.2.trans_lt hβv),
    A.triangle_section_eq_edgeLevels (by rwa [hq]) hβu hβv, image_segment,
    A.homothety_zero_edgeLevel hq hβ.ne', A.homothety_zero_edgeLevel hq hβ.ne']

end AffineMap
