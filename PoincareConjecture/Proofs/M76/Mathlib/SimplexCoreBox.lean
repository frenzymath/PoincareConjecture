import PoincareConjecture.Proofs.M76.Mathlib.StdSimplexCore
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

open Set

namespace StdSimplexCore

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

def boxRegion (η : ℝ) : Set ((ι → ℝ) × (κ → ℝ)) :=
  {z | (∀ i, η ≤ z.1 i) ∧ z.2 ∈ Icc 0 (fun _ => η) ∧
    (∑ i, z.1 i) + ∑ j, z.2 j = 1}

variable {κ}

noncomputable def boxScale (η : ℝ) (v : κ → ℝ) : ℝ :=
  1 - (∑ j, v j) / (1 - (Fintype.card ι : ℝ) * η)

variable {ι}

theorem boxDenominator_pos {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1) :
    0 < 1 - (Fintype.card ι : ℝ) * η := by
  have hκ : 0 ≤ (Fintype.card κ : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη
  nlinarith [hbound]

theorem boxScale_pos {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    {v : κ → ℝ} (hv : v ∈ Icc 0 (fun _ => η)) : 0 < boxScale ι η v := by
  have hden := boxDenominator_pos hη hbound
  have hsum : (∑ j, v j) ≤ (Fintype.card κ : ℝ) * η := by
    calc
      (∑ j, v j) ≤ ∑ _j : κ, η := Finset.sum_le_sum (fun j _ => hv.2 j)
      _ = (Fintype.card κ : ℝ) * η := by simp
  rw [boxScale, sub_pos, div_lt_one hden]
  nlinarith [hbound, hsum]

theorem boxScale_mul {η : ℝ} (hden : 1 - (Fintype.card ι : ℝ) * η ≠ 0)
    (v : κ → ℝ) :
    boxScale ι η v * (1 - (Fintype.card ι : ℝ) * η) =
      1 - (Fintype.card ι : ℝ) * η - ∑ j, v j := by
  rw [boxScale, sub_mul, one_mul, div_mul_cancel₀ _ hden]

theorem continuous_boxScale (ι : Type*) [Fintype ι] (η : ℝ) :
    Continuous (boxScale ι η : (κ → ℝ) → ℝ) := by
  unfold boxScale
  fun_prop

variable (ι κ)

noncomputable def boxPoint (η : ℝ) (q : ι → ℝ) (v : κ → ℝ) :
    (ι → ℝ) × (κ → ℝ) :=
  (fun i => η + boxScale ι η v * (q i - η), v)

noncomputable def boxBase (η : ℝ) (z : (ι → ℝ) × (κ → ℝ)) : ι → ℝ :=
  fun i => η + (z.1 i - η) / boxScale ι η z.2

variable {ι κ}

theorem boxPoint_mem {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    {q : ι → ℝ} (hq : q ∈ stdSimplexCore ι η)
    {v : κ → ℝ} (hv : v ∈ Icc 0 (fun _ => η)) :
    boxPoint ι κ η q v ∈ boxRegion ι κ η := by
  have ha := boxScale_pos hη hbound hv
  refine ⟨fun i => ?_, hv, ?_⟩
  · change η ≤ η + boxScale ι η v * (q i - η)
    exact le_add_of_nonneg_right (mul_nonneg ha.le (sub_nonneg.mpr (hq.1 i)))
  · change (∑ i, (η + boxScale ι η v * (q i - η))) + ∑ j, v j = 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hq.2]
    rw [boxScale_mul (boxDenominator_pos hη hbound).ne']
    ring

theorem boxBase_mem {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    {z : (ι → ℝ) × (κ → ℝ)} (hz : z ∈ boxRegion ι κ η) :
    boxBase ι κ η z ∈ stdSimplexCore ι η := by
  have ha := boxScale_pos hη hbound hz.2.1
  have hsum : (∑ i, z.1 i) - (Fintype.card ι : ℝ) * η =
      boxScale ι η z.2 * (1 - (Fintype.card ι : ℝ) * η) := by
    rw [boxScale_mul (boxDenominator_pos hη hbound).ne']
    linarith [hz.2.2]
  refine ⟨fun i => ?_, ?_⟩
  · change η ≤ η + (z.1 i - η) / boxScale ι η z.2
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (hz.1 i)) ha.le)
  · change (∑ i, (η + (z.1 i - η) / boxScale ι η z.2)) = 1
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hsum, mul_div_cancel_left₀ _ ha.ne']
    ring

theorem boxBase_boxPoint (η : ℝ) (q : ι → ℝ) (v : κ → ℝ)
    (ha : boxScale ι η v ≠ 0) :
    boxBase ι κ η (boxPoint ι κ η q v) = q := by
  funext i
  simp only [boxBase, boxPoint, add_sub_cancel_left]
  rw [mul_div_cancel_left₀ _ ha]
  ring

theorem boxPoint_boxBase (η : ℝ) (z : (ι → ℝ) × (κ → ℝ))
    (ha : boxScale ι η z.2 ≠ 0) :
    boxPoint ι κ η (boxBase ι κ η z) z.2 = z := by
  apply Prod.ext
  · funext i
    simp only [boxPoint, boxBase, add_sub_cancel_left]
    rw [mul_div_cancel₀ _ ha]
    ring
  · rfl

end StdSimplexCore
