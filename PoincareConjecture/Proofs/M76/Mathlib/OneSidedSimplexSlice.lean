import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroCrossing
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

open Set
open scoped BigOperators

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem weighted_zeroCrossing (A : E →ᵃ[ℝ] ℝ) {u v : E} (w : ℝ)
    (hu : A u < 0) (hv : 0 < A v) :
    (w * (A v - A u) / A v) • A.zeroCrossing u v =
      w • u + (-w * A u / A v) • v := by
  have hgap : A v - A u ≠ 0 := ne_of_gt (by linarith)
  simp only [zeroCrossing, lineMap_apply_module, smul_add, smul_smul]
  congr 1
  · congr 1
    field_simp [hgap, hv.ne']
    ring
  · congr 1
    field_simp [hgap, hv.ne']

theorem convexHull_insert_inter_zero (A : E →ᵃ[ℝ] ℝ) (s : Finset E) {v : E}
    (hs : ∀ u ∈ s, A u < 0) (hv : 0 < A v) :
    convexHull ℝ (insert v (s : Set E)) ∩ {x | A x = 0} =
      convexHull ℝ ((fun u => A.zeroCrossing u v) '' (s : Set E)) := by
  classical
  have hvs : v ∉ s := fun h => (hs v h).not_gt hv
  apply Subset.antisymm
  · rintro x ⟨hx, hAx⟩
    change A x = 0 at hAx
    have hxt : x ∈ convexHull ℝ ((insert v s : Finset E) : Set E) := by
      simpa only [Finset.coe_insert] using hx
    obtain ⟨w, hw, hsum, hval⟩ := Finset.mem_convexHull'.mp hxt
    have hheight := (insert v s).map_affineCombination (fun u : E => u) w hsum A
    simp only [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
      Function.comp_apply, smul_eq_mul, hval, hAx] at hheight
    have hsum' : w v + ∑ u ∈ s, w u = 1 := by
      simpa only [Finset.sum_insert hvs] using hsum
    have hheight' : w v * A v + ∑ u ∈ s, w u * A u = 0 := by
      simpa only [Finset.sum_insert hvs] using hheight.symm
    let k : E → ℝ := fun u => w u * (A v - A u) / A v
    have hksum : ∑ u ∈ s, k u = 1 := by
      simp only [k, mul_sub, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
      apply (div_eq_one_iff_eq hv.ne').mpr
      nlinarith [hsum', hheight']
    have hvsum : (∑ u ∈ s, -w u * A u / A v) = w v := by
      simp only [neg_mul, ← Finset.sum_div, Finset.sum_neg_distrib]
      apply (div_eq_iff hv.ne').mpr
      linarith
    apply mem_convexHull_of_exists_fintype (fun u : s => k u)
      (fun u : s => A.zeroCrossing u v)
    · intro u
      exact div_nonneg (mul_nonneg (hw u (Finset.mem_insert_of_mem u.property))
        (sub_nonneg.mpr ((hs u u.property).le.trans hv.le))) hv.le
    · simpa only [Finset.sum_coe_sort] using hksum
    · intro u
      exact mem_image_of_mem _ u.property
    · change (∑ u : s, k u • A.zeroCrossing u v) = x
      rw [Finset.sum_coe_sort s (fun u => k u • A.zeroCrossing u v)]
      have he : (∑ u ∈ s, k u • A.zeroCrossing u v) =
          (∑ u ∈ s, w u • u) + w v • v := by
        calc
          _ = ∑ u ∈ s, (w u • u + (-w u * A u / A v) • v) :=
            Finset.sum_congr rfl (fun u hu => weighted_zeroCrossing A _ (hs u hu) hv)
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_smul, hvsum]
      rw [he, add_comm]
      simpa only [Finset.sum_insert hvs] using hval
  · apply convexHull_min
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨?_, A.zeroCrossing_apply (ne_of_lt ((hs u hu).trans hv))⟩
      apply convexHull_mono (s := ({u, v} : Set E)) (by
        intro y hy
        rcases hy with rfl | rfl
        · exact mem_insert_of_mem _ hu
        · exact mem_insert _ _)
      rw [convexHull_pair]
      exact openSegment_subset_segment ℝ u v (A.zeroCrossing_mem_openSegment (hs u hu) hv)
    · exact (convex_convexHull ℝ _).inter ((convex_singleton (0 : ℝ)).affine_preimage A)

end AffineMap
