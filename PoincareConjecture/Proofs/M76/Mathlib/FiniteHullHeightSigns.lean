import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns
import Mathlib.Data.Finset.Max












set_option autoImplicit false

open Set

namespace Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem eq_of_mem_convexHull_of_injective_affine_minimum
    (s : Finset E) (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A (s : Set E))
    {v x : E} (hv : v ∈ s) (hmin : ∀ w ∈ s, A v ≤ A w)
    (hx : x ∈ convexHull ℝ (s : Set E)) (hAx : A x = A v) : x = v := by
  let B := A - AffineMap.const ℝ E (A v)
  have hB : ∀ w ∈ s, 0 ≤ B w := fun w hw => sub_nonneg.mpr (hmin w hw)
  have hxB : B x = 0 := sub_eq_zero.mpr hAx
  have hzero := s.mem_convexHull_zero_vertices B hB hx hxB
  have hsingle : (s : Set E) ∩ {w | B w = 0} ⊆ {v} := by
    intro w hw
    exact hA hw.1 hv (sub_eq_zero.mp hw.2)
  have h := convexHull_mono hsingle hzero
  simpa only [convexHull_singleton, mem_singleton_iff] using h





theorem mem_both_height_closures_of_distinct_level_points
    (s : Finset E) (hs : s.Nonempty) (A : E →ᵃ[ℝ] ℝ)
    (hA : InjOn A (s : Set E)) {x y : E}
    (hx : x ∈ convexHull ℝ (s : Set E))
    (hy : y ∈ convexHull ℝ (s : Set E)) (hxy : x ≠ y) (hAy : A y = A x) :
    x ∈ closure (convexHull ℝ (s : Set E) ∩ {z | A z < A x}) ∧
      x ∈ closure (convexHull ℝ (s : Set E) ∩ {z | A x < A z}) := by
  obtain ⟨v, hv, hmin⟩ := s.exists_min_image A hs
  obtain ⟨w, hw, hmax⟩ := s.exists_max_image A hs
  have hlo : A v ≤ A x :=
    convexHull_min (fun z hz => hmin z hz) ((convex_Ici (A v)).affine_preimage A) hx
  have hhi : A x ≤ A w :=
    convexHull_min (fun z hz => hmax z hz) ((convex_Iic (A w)).affine_preimage A) hx
  have hlow : A v < A x := by
    apply lt_of_le_of_ne hlo
    intro heq
    have hxv := s.eq_of_mem_convexHull_of_injective_affine_minimum A hA hv hmin hx heq.symm
    have hyv := s.eq_of_mem_convexHull_of_injective_affine_minimum A hA hv hmin hy
      (hAy.trans heq.symm)
    exact hxy (hxv.trans hyv.symm)
  have hneg : InjOn (-A) (s : Set E) := by
    intro u hu v hv huv
    exact hA hu hv (neg_injective huv)
  have hhigh : A x < A w := by
    apply lt_of_le_of_ne hhi
    intro heq
    have hminNeg : ∀ z ∈ s, (-A) w ≤ (-A) z :=
      fun z hz => neg_le_neg (hmax z hz)
    have hxw := s.eq_of_mem_convexHull_of_injective_affine_minimum (-A) hneg hw hminNeg
      hx (congrArg Neg.neg heq)
    have hyw := s.eq_of_mem_convexHull_of_injective_affine_minimum (-A) hneg hw hminNeg
      hy (congrArg Neg.neg (hAy.trans heq))
    exact hxy (hxw.trans hyw.symm)
  exact ⟨(convex_convexHull ℝ _).mem_closure_lower_affine_height A hx
      (subset_convexHull ℝ _ hv) hlow,
    (convex_convexHull ℝ _).mem_closure_upper_affine_height A hx
      (subset_convexHull ℝ _ hw) hhigh⟩

end Finset
