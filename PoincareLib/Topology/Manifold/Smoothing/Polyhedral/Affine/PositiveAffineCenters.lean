import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive simplex centers on an affine hyperplane

An opposite-sign segment from a simplex point to a positive center
crosses the hyperplane at another positive center. This is the
center-selection step of Hudson 1969, Lemma 1.5, pp. 12--13;
see M76 derivation 75.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A segment from a simplex point to a positive center crosses
an affine hyperplane at a positive center when the endpoint values
have opposite signs. See Hudson pp. 12--13 and M76 derivation 75. -/
theorem exists_positive_center_affine_zero (s : Finset E) (A : E →ᵃ[ℝ] ℝ)
    {c x : E}
    (hc : ∃ u : E → ℝ, (∀ v ∈ s, 0 < u v) ∧
      (∑ v ∈ s, u v) = 1 ∧ (∑ v ∈ s, u v • v) = c)
    (hx : x ∈ convexHull ℝ (s : Set E)) (hAx : A x < 0) (hAc : 0 < A c) :
    ∃ z : E, (∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
      (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = z) ∧ A z = 0 := by
  obtain ⟨u, hu, husum, huval⟩ := hc
  obtain ⟨w, hw, hwsum, hwval⟩ := mem_convexHull'.mp hx
  let r : ℝ := -A x / (A c - A x)
  have hden : 0 < A c - A x := by linarith
  have hr : 0 < r := div_pos (neg_pos.mpr hAx) hden
  have hr1 : r < 1 := (div_lt_one hden).mpr (by linarith)
  refine ⟨AffineMap.lineMap x c r,
    ⟨fun v => (1 - r) * w v + r * u v, ?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_pos.mpr hr1).le (hw v hv))
      (mul_pos hr (hu v hv))
  · simp only [sum_add_distrib, ← mul_sum, hwsum, husum, mul_one]
    ring
  · simp only [add_smul, mul_smul, sum_add_distrib, ← smul_sum, hwval, huval,
      AffineMap.lineMap_apply_module]
  · rw [A.apply_lineMap, AffineMap.lineMap_apply_ring']
    dsimp only [r]
    field_simp
    ring

/-- Nested positive centers selected on a hyperplane whenever
possible cannot lie strictly on opposite sides. See Hudson
pp. 12--13 and M76 derivation 75. -/
theorem positive_centers_same_side {s t : Finset E} (hst : s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {x y : E}
    (hx : ∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
      (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = x)
    (hy : ∃ w : E → ℝ, (∀ v ∈ t, 0 < w v) ∧
      (∑ v ∈ t, w v) = 1 ∧ (∑ v ∈ t, w v • v) = y)
    (hzero : (∃ z : E, (∃ w : E → ℝ, (∀ v ∈ t, 0 < w v) ∧
      (∑ v ∈ t, w v) = 1 ∧ (∑ v ∈ t, w v • v) = z) ∧ A z = 0) → A y = 0) :
    (A x ≤ 0 ∧ A y ≤ 0) ∨ (0 ≤ A x ∧ 0 ≤ A y) := by
  have hxt : x ∈ convexHull ℝ (t : Set E) := by
    obtain ⟨w, hw, hsum, hval⟩ := hx
    exact convexHull_mono hst
      (mem_convexHull'.mpr ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩)
  have hnegpos : ¬(A x < 0 ∧ 0 < A y) := by
    rintro ⟨hAx, hAy⟩
    have he := hzero (t.exists_positive_center_affine_zero A hy hxt hAx hAy)
    linarith
  have hposneg : ¬(0 < A x ∧ A y < 0) := by
    rintro ⟨hAx, hAy⟩
    obtain ⟨z, hz, hAz⟩ := t.exists_positive_center_affine_zero (-A) hy hxt
      (by change -A x < 0; linarith) (by change 0 < -A y; linarith)
    change -(A z) = 0 at hAz
    have he := hzero ⟨z, hz, neg_eq_zero.mp hAz⟩
    linarith
  rcases le_total (A x) 0 with h | h
  · by_cases hy0 : A y ≤ 0
    · exact Or.inl ⟨h, hy0⟩
    · exact Or.inr ⟨by by_contra hx0; exact hnegpos ⟨lt_of_not_ge hx0, lt_of_not_ge hy0⟩,
        (lt_of_not_ge hy0).le⟩
  · by_cases hy0 : 0 ≤ A y
    · exact Or.inr ⟨h, hy0⟩
    · exact Or.inl ⟨by by_contra hx0; exact hposneg ⟨lt_of_not_ge hx0, lt_of_not_ge hy0⟩,
        (lt_of_not_ge hy0).le⟩

end Finset
