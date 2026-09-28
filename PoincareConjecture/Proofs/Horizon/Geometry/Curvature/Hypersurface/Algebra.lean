import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace Poincare.Geometry.Curvature.Hypersurface

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def negativePart (x : ℝ) : ℝ := max 0 (-x)

lemma negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := by
  exact le_max_left _ _

lemma neg_le_negativePart (x : ℝ) : -x ≤ negativePart x := by
  exact le_max_right _ _

lemma principal_curvature_lower_bound
    (κ : ι → ℝ) (i : ι) (H β : ℝ) {m : ℕ}
    (htrace : H = ∑ j, κ j)
    (_hupper : ∀ j, κ j ≤ β)
    (hrest : (∑ j ∈ Finset.univ.erase i, κ j) ≤ (m : ℝ) * β)
    (_hm : 0 ≤ β) :
    -(negativePart H) - (m : ℝ) * β ≤ κ i := by
  have hsum : (∑ j, κ j) = κ i + ∑ j ∈ Finset.univ.erase i, κ j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hi : κ i = H - ∑ j ∈ Finset.univ.erase i, κ j := by
    rw [htrace, hsum]
    ring
  rw [hi]
  linarith [hrest, neg_le_negativePart H]

lemma principal_curvature_lower_bound_of_card
    {m : ℕ} (κ : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (H β : ℝ)
    (htrace : H = ∑ j, κ j)
    (hupper : ∀ j, κ j ≤ β) (hm : 0 ≤ β) :
    -(negativePart H) - (m : ℝ) * β ≤ κ i := by
  apply principal_curvature_lower_bound κ i H β htrace hupper
  · calc
      (∑ j ∈ Finset.univ.erase i, κ j) ≤
          (∑ _j ∈ Finset.univ.erase i, β) :=
        Finset.sum_le_sum fun j hj => hupper j
      _ = (m : ℝ) * β := by
        rw [Finset.sum_const]
        simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  · exact hm

lemma principal_curvature_product_lower_bound
    {a b H β : ℝ} {m : ℕ}
    (ha : -(negativePart H) - (m : ℝ) * β ≤ a) (ha' : a ≤ β)
    (hb : -(negativePart H) - (m : ℝ) * β ≤ b) (hb' : b ≤ β)
    (hm : 0 ≤ β) :
    -(negativePart H + (m : ℝ) * β) * β ≤ a * b := by
  have hL : -(negativePart H) - (m : ℝ) * β ≤ 0 := by
    have hm' : 0 ≤ (m : ℝ) * β := mul_nonneg (Nat.cast_nonneg m) hm
    linarith [negativePart_nonneg H, hm']
  by_cases hb0 : 0 ≤ b
  · by_cases ha0 : 0 ≤ a
    · have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
      have htarget : -(negativePart H + (m : ℝ) * β) * β ≤ 0 := by
        have hsum : 0 ≤ negativePart H + (m : ℝ) * β := by
          exact add_nonneg (negativePart_nonneg H)
            (mul_nonneg (Nat.cast_nonneg m) hm)
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsum) hm
      linarith
    · have hmul : (-(negativePart H) - (m : ℝ) * β) * b ≤ a * b :=
        mul_le_mul_of_nonneg_right ha hb0
      have hmul' : -(negativePart H + (m : ℝ) * β) * β ≤
          (-(negativePart H) - (m : ℝ) * β) * b := by
        nlinarith [hb', hm, negativePart_nonneg H]
      exact hmul'.trans hmul
  · have hbneg : b ≤ 0 := le_of_not_ge hb0
    have hmul : β * b ≤ a * b :=
      mul_le_mul_of_nonpos_right ha' hbneg
    have hmul' : -(negativePart H + (m : ℝ) * β) * β ≤ β * b := by
      nlinarith [hb, hm, negativePart_nonneg H]
    exact hmul'.trans hmul

lemma principal_curvature_pair_lower_bound_of_card
    {m : ℕ} (κ : Fin (m + 1) → ℝ) (i j : Fin (m + 1)) (H β : ℝ)
    (htrace : H = ∑ k, κ k) (hupper : ∀ k, κ k ≤ β) (hβ : 0 ≤ β) :
    -(negativePart H + (m : ℝ) * β) * β ≤ κ i * κ j := by
  apply principal_curvature_product_lower_bound
  · exact principal_curvature_lower_bound_of_card κ i H β htrace hupper hβ
  · exact hupper i
  · exact principal_curvature_lower_bound_of_card κ j H β htrace hupper hβ
  · exact hupper j
  · exact hβ

lemma diagonal_extrinsic_determinant_eq_half_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ u v : ι → ℝ) :
    (∑ i, κ i * u i ^ 2) * (∑ j, κ j * v j ^ 2) -
        (∑ i, κ i * u i * v i) ^ 2 =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        κ i * κ j * (u i * v j - u j * v i) ^ 2 := by
  have hprod (f g : ι → ℝ) :
      (∑ i, f i) * (∑ j, g j) = ∑ i, ∑ j, f i * g j := by
    rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hswap (f : ι → ι → ℝ) :
      (∑ i, ∑ j, f i j) = ∑ i, ∑ j, f j i := by
    rw [Finset.sum_comm]
  have hA := hswap (fun i j => κ i * u i ^ 2 * (κ j * v j ^ 2))
  have hcross :
      (∑ i, ∑ j, (κ i * u i * v i) * (κ j * u j * v j)) =
        ∑ i, ∑ j, κ i * κ j * (u i * v j * (u j * v i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hA0 :
      (∑ i, ∑ j, (κ i * u i ^ 2) * (κ j * v j ^ 2)) =
        ∑ i, ∑ j, κ i * κ j * (u i * v j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hB0 :
      (∑ i, ∑ j, (κ j * u j ^ 2) * (κ i * v i ^ 2)) =
        ∑ i, ∑ j, κ i * κ j * (u j * v i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hhalf (i j : ι) :
      (1 / 2 : ℝ) * (κ i * κ j * (u i * v j - u j * v i) ^ 2) =
        (1 / 2 : ℝ) * (κ i * κ j * (u i * v j) ^ 2) -
          (κ i * κ j * (u i * v j * (u j * v i))) +
            (1 / 2 : ℝ) * (κ i * κ j * (u j * v i) ^ 2) := by
    ring
  calc
    _ = (∑ i, ∑ j, (κ i * u i ^ 2) * (κ j * v j ^ 2)) -
          (∑ i, ∑ j, (κ i * u i * v i) * (κ j * u j * v j)) := by
      simp only [pow_two]
      rw [hprod, hprod]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j,
          κ i * κ j * (u i * v j - u j * v i) ^ 2 := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      simp_rw [hhalf]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hA0]
      rw [hA0, hB0] at hA
      rw [hcross]
      simp only [← Finset.mul_sum]
      linear_combination (1 / 2 : ℝ) * hA

lemma diagonal_extrinsic_determinant_lower_bound_of_card
    {m : ℕ} (κ u v : Fin (m + 1) → ℝ) (H β : ℝ)
    (htrace : H = ∑ i, κ i) (hupper : ∀ i, κ i ≤ β) (hβ : 0 ≤ β)
    (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1)
    (huv : ∑ i, u i * v i = 0) :
    -(negativePart H + (m : ℝ) * β) * β ≤
      (∑ i, κ i * u i ^ 2) * (∑ j, κ j * v j ^ 2) -
        (∑ i, κ i * u i * v i) ^ 2 := by
  have hpair (i j : Fin (m + 1)) :
      -(negativePart H + (m : ℝ) * β) * β ≤ κ i * κ j :=
    principal_curvature_pair_lower_bound_of_card κ i j H β htrace hupper hβ
  have hterm (i j : Fin (m + 1)) :
      (-(negativePart H + (m : ℝ) * β) * β) *
          (u i * v j - u j * v i) ^ 2 ≤
        κ i * κ j * (u i * v j - u j * v i) ^ 2 := by
    exact mul_le_mul_of_nonneg_right (hpair i j) (sq_nonneg _)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i hi =>
    Finset.sum_le_sum (s := Finset.univ) fun j hj => hterm i j
  have hminor :
      ∑ i, ∑ j, (u i * v j - u j * v i) ^ 2 = 2 := by
    have hid := diagonal_extrinsic_determinant_eq_half_sum (fun _ => 1) u v
    simp only [one_mul, hu, hv, huv] at hid
    linarith
  rw [diagonal_extrinsic_determinant_eq_half_sum]
  have hscaled := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [← Finset.mul_sum] at hscaled
  rw [hminor] at hscaled
  nlinarith

theorem sectional_lower_bound_of_gauss
    {K β H : ℝ} {m : ℕ} {Plane : Type*}
    (_hK : 0 ≤ K) (_hβ : 0 ≤ β)
    (ambient extrinsic induced : Plane → ℝ)
    (hambient : ∀ P, -K ≤ ambient P)
    (hgauss : ∀ P, induced P = ambient P + extrinsic P)
    (hextrinsic : ∀ P, -(negativePart H + (m : ℝ) * β) * β ≤ extrinsic P) :
    ∀ P, -K - (negativePart H + (m : ℝ) * β) * β ≤ induced P := by
  intro P
  rw [hgauss P]
  linarith [hambient P, hextrinsic P]

end Poincare.Geometry.Curvature.Hypersurface
