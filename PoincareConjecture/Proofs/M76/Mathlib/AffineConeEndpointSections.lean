import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeAffine
import PoincareConjecture.Proofs.M76.Mathlib.HeightSeparatedSets










set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem convexJoin_inter_base_level (A : E →ᵃ[ℝ] ℝ) {p : E} {d : Set E} {c : ℝ}
    (hpc : A p ≠ c) (hd : ∀ x ∈ d, A x = c) :
    convexJoin ℝ {p} d ∩ {x | A x = c} = d := by
  apply Subset.antisymm
  · rintro x ⟨hx, hAx⟩
    obtain ⟨u, hu, y, hy, hxy⟩ := mem_convexJoin.mp hx
    have hup : u = p := hu
    subst u
    rw [segment_eq_image_lineMap] at hxy
    obtain ⟨r, _, rfl⟩ := hxy
    change A (AffineMap.lineMap p y r) = c at hAx
    rw [A.apply_lineMap, hd y hy, AffineMap.lineMap_apply_ring'] at hAx
    have hmul : (r - 1) * (c - A p) = 0 := by nlinarith
    have hr : r = 1 := sub_eq_zero.mp
      ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hpc.symm))
    simpa only [hr, AffineMap.lineMap_apply_one] using hy
  · intro x hx
    exact ⟨mem_convexJoin.mpr ⟨p, mem_singleton p, x, hx, right_mem_segment ℝ p x⟩,
      hd x hx⟩





theorem convexJoin_inter_apex_level (A : E →ᵃ[ℝ] ℝ) {p : E} {d : Set E} {c : ℝ}
    (hpc : A p ≠ c) (hd : ∀ x ∈ d, A x = c) (hne : d.Nonempty) :
    convexJoin ℝ {p} d ∩ {x | A x = A p} = {p} := by
  apply Subset.antisymm
  · rintro x ⟨hx, hAx⟩
    obtain ⟨u, hu, y, hy, hxy⟩ := mem_convexJoin.mp hx
    have hup : u = p := hu
    subst u
    rw [segment_eq_image_lineMap] at hxy
    obtain ⟨r, _, rfl⟩ := hxy
    change A (AffineMap.lineMap p y r) = A p at hAx
    rw [A.apply_lineMap, hd y hy, AffineMap.lineMap_apply_ring'] at hAx
    have hmul : r * (c - A p) = 0 := by linarith
    have hr : r = 0 := (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hpc.symm)
    simpa only [hr, AffineMap.lineMap_apply_zero] using (mem_singleton p)
  · intro x hx
    have hxp : x = p := hx
    subst x
    obtain ⟨y, hy⟩ := hne
    exact ⟨mem_convexJoin.mpr ⟨p, mem_singleton p, y, hy, left_mem_segment ℝ p y⟩, rfl⟩

end AffineMap
