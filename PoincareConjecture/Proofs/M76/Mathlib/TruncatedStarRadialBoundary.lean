import PoincareConjecture.Proofs.M76.Mathlib.RadialStar











set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]




def truncatedStarBoundary (K : SimplicialComplex ℝ E) (L : E →ₗ[ℝ] ℝ)
    (α β : ℝ) : Set E :=
  ((K.closedStar 0).space ∩ {x | L x = α}) ∪
    ((K.closedStar 0).space ∩ {x | L x = β}) ∪
    ((K.link 0).space ∩ {x | L x ∈ Icc α β})



theorem truncatedStarBoundary_subset_band (K : SimplicialComplex ℝ E)
    (L : E →ₗ[ℝ] ℝ) {α β : ℝ} (hαβ : α ≤ β) :
    K.truncatedStarBoundary L α β ⊆
      (K.closedStar 0).space ∩ {x | L x ∈ Icc α β} := by
  rintro x ((hx | hx) | hx)
  · refine ⟨hx.1, ?_⟩
    change α ≤ L x ∧ L x ≤ β
    rw [show L x = α from hx.2]
    exact ⟨le_rfl, hαβ⟩
  · refine ⟨hx.1, ?_⟩
    change α ≤ L x ∧ L x ≤ β
    rw [show L x = β from hx.2]
    exact ⟨hαβ, le_rfl⟩
  · obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1
    exact ⟨convexHull_subset_space (K.link_le_closedStar 0 hs) hxs, hx.2⟩



theorem zero_notMem_truncatedStarBoundary (K : SimplicialComplex ℝ E)
    (L : E →ₗ[ℝ] ℝ) {α β : ℝ} (hα : α < 0) (hβ : 0 < β) :
    (0 : E) ∉ K.truncatedStarBoundary L α β := by
  rintro ((h | h) | h)
  · exact hα.ne (by simpa only [map_zero] using (show L 0 = α from h.2).symm)
  · exact hβ.ne (by simpa only [map_zero] using (show L 0 = β from h.2))
  · exact K.zero_notMem_link_space h.1





theorem eq_one_of_smul_mem_truncatedStarBoundary
    (K : SimplicialComplex ℝ E) (L : E →ₗ[ℝ] ℝ) {α β : ℝ}
    (hα : α < 0) (hβ : 0 < β) {x : E}
    (hx : x ∈ (K.closedStar 0).space ∩ {x | L x ∈ Icc α β})
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1)
    (hrx : r • x ∈ K.truncatedStarBoundary L α β) : r = 1 := by
  rcases hrx with (hlo | hhi) | hlink
  · have heq : r * L x = α := by
      simpa only [map_smul, smul_eq_mul] using (show L (r • x) = α from hlo.2)
    have hmul : 0 ≤ r * (L x - α) := mul_nonneg hr.1.le (sub_nonneg.mpr hx.2.1)
    nlinarith [hr.2]
  · have heq : r * L x = β := by
      simpa only [map_smul, smul_eq_mul] using (show L (r • x) = β from hhi.2)
    have hmul : 0 ≤ r * (β - L x) := mul_nonneg hr.1.le (sub_nonneg.mpr hx.2.2)
    nlinarith [hr.2]
  · have hx0 : x ≠ 0 := by
      intro h
      exact K.zero_notMem_link_space (by simpa only [h, smul_zero] using hlink.1)
    obtain ⟨y, hy, a, ha, hxy⟩ := exists_linkPoint_smul hx.1 hx0
    have hy0 : y ≠ 0 := fun h => K.zero_notMem_link_space (h ▸ hy)
    have heq : r • x = y := by
      apply K.injOn_normalize_link hlink.1 hy
      rw [normalize_smul_of_pos hr.1, hxy, normalize_smul_of_pos ha.1]
    have hprod : r * a = 1 := by
      apply smul_left_injective ℝ hy0
      simpa only [hxy, smul_smul, one_smul] using heq
    have hbound : r * a ≤ r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ha.2 hr.1.le
    exact le_antisymm hr.2 (hprod ▸ hbound)




theorem injOn_normalize_truncatedStarBoundary (K : SimplicialComplex ℝ E)
    (L : E →ₗ[ℝ] ℝ) {α β : ℝ} (hα : α < 0) (hβ : 0 < β) :
    InjOn (normalize : E → E) (K.truncatedStarBoundary L α β) := by
  have hband := K.truncatedStarBoundary_subset_band L (hα.trans hβ).le
  have hzero := K.zero_notMem_truncatedStarBoundary L hα hβ
  have hcase (x y : E) (hx : x ∈ K.truncatedStarBoundary L α β)
      (hy : y ∈ K.truncatedStarBoundary L α β)
      (hxy : normalize x = normalize y) (hle : ‖x‖ ≤ ‖y‖) : x = y := by
    have hx0 : x ≠ 0 := fun h => hzero (h ▸ hx)
    have hy0 : y ≠ 0 := fun h => hzero (h ▸ hy)
    have hratio : ‖x‖ / ‖y‖ ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0),
        (div_le_one (norm_pos_iff.mpr hy0)).mpr hle⟩
    have heq : (‖x‖ / ‖y‖) • y = x := by
      calc
        (‖x‖ / ‖y‖) • y = ‖x‖ • normalize y := by
          rw [NormedSpace.normalize, smul_smul, div_eq_mul_inv]
        _ = ‖x‖ • normalize x := by rw [hxy]
        _ = x := norm_smul_normalize x
    have hone := K.eq_one_of_smul_mem_truncatedStarBoundary L hα hβ (hband hy)
      hratio (heq.symm ▸ hx)
    simpa only [hone, one_smul] using heq.symm
  intro x hx y hy hxy
  rcases le_total ‖x‖ ‖y‖ with hle | hle
  · exact hcase x y hx hy hxy hle
  · exact (hcase y x hy hx hxy.symm hle).symm

end Geometry.SimplicialComplex
