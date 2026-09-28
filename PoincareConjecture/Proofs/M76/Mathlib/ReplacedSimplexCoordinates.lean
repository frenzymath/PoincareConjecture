import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open Set

namespace AffineBasis

variable {ι E : Type*} [Finite ι] [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

theorem mem_convexHull_update_of_coord (b : AffineBasis ι ℝ E) (i : ι) (q y : E)
    (hqi : b.coord i q ≠ 0) (hc : 0 ≤ b.coord i y / b.coord i q)
    (hw : ∀ j, j ≠ i → 0 ≤ b.coord j y - (b.coord i y / b.coord i q) * b.coord j q) :
    y ∈ convexHull ℝ (range (Function.update b i q)) := by
  let : Fintype ι := Fintype.ofFinite ι
  let c := b.coord i y / b.coord i q
  let d : ι → ℝ := fun j => b.coord j y - c * b.coord j q
  have hdi : d i = 0 := by
    dsimp only [d, c]
    rw [div_mul_cancel₀ _ hqi, sub_self]
  let w : ι → ℝ := fun j => d j + if j = i then c else 0
  have hsumd : ∑ j, d j = 1 - c := by
    simp only [d, Finset.sum_sub_distrib, ← Finset.mul_sum, b.sum_coord_apply_eq_one, mul_one]
  have hsumw : ∑ j, w j = 1 := by
    simp only [w, Finset.sum_add_distrib, hsumd, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [w, hdi, ite_true, zero_add] using hc
    · simpa only [w, if_neg hji, add_zero] using hw j hji
  have he (j : ι) : w j • Function.update b i q j =
      d j • b j + if j = i then c • q else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [w, hdi, ite_true, zero_add, zero_smul, Function.update_self]
    · simp only [w, if_neg hji, add_zero, Function.update_of_ne hji]
  have hsum : ∑ j, w j • Function.update b i q j = y := by
    simp only [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [d, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
      b.linear_combination_coord_eq_self, sub_add_cancel]
  exact mem_convexHull_of_exists_fintype w (Function.update b i q) hw0 hsumw
    (fun j => mem_range_self j) hsum

end AffineBasis
