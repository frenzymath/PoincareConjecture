import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal

namespace Poincare.MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem lintegral_cost_convolution_le
    {d K L : X → X → ℝ≥0∞}
    (hd : Measurable (Function.uncurry d))
    (hL : Measurable (Function.uncurry L))
    (htri : ∀ x z y, d x y ≤ d x z + d z y)
    (hK : ∀ x, Measurable (K x))
    (hmK : ∀ x, ∫⁻ y, K x y ∂μ ≤ 1)
    (hmL : ∀ x, ∫⁻ y, L x y ∂μ ≤ 1)
    {A B : ℝ≥0∞}
    (hA : ∀ x, ∫⁻ y, d x y * K x y ∂μ ≤ A)
    (hB : ∀ x, ∫⁻ y, d x y * L x y ∂μ ≤ B) (x : X) :
    ∫⁻ y, d x y * (∫⁻ z, K x z * L z y ∂μ) ∂μ ≤ A + B := by
  have hdrow (z : X) : Measurable (d z) := hd.comp measurable_prodMk_left
  have hLrow (z : X) : Measurable (L z) := hL.comp measurable_prodMk_left
  calc
    ∫⁻ y, d x y * (∫⁻ z, K x z * L z y ∂μ) ∂μ =
        ∫⁻ y, ∫⁻ z, d x y * (K x z * L z y) ∂μ ∂μ := by
      apply lintegral_congr
      intro y
      exact (lintegral_const_mul _
        ((hK x).mul (hL.comp measurable_prodMk_right))).symm
    _ = ∫⁻ z, ∫⁻ y, d x y * (K x z * L z y) ∂μ ∂μ := by
      exact lintegral_lintegral_swap
        (((hdrow x).comp measurable_fst).mul
          (((hK x).comp measurable_snd).mul (hL.comp measurable_swap))).aemeasurable
    _ ≤ ∫⁻ z, d x z * K x z + K x z * B ∂μ := by
      apply lintegral_mono
      intro z
      calc
        ∫⁻ y, d x y * (K x z * L z y) ∂μ ≤
            ∫⁻ y, (d x z + d z y) * (K x z * L z y) ∂μ :=
          lintegral_mono fun y => mul_le_mul_left (htri x z y) _
        _ = d x z * K x z * (∫⁻ y, L z y ∂μ) +
            K x z * (∫⁻ y, d z y * L z y ∂μ) := by
          simp_rw [add_mul, ← mul_assoc]
          rw [lintegral_add_left
            ((hLrow z).const_mul (d x z * K x z))]
          rw [lintegral_const_mul _ (hLrow z)]
          congr 1
          simp_rw [mul_comm (d z _) (K x z), mul_assoc]
          exact lintegral_const_mul _ ((hdrow z).mul (hLrow z))
        _ ≤ d x z * K x z + K x z * B := by
          simpa only [mul_one] using
            add_le_add (mul_le_mul_right (hmL z) _) (mul_le_mul_right (hB z) _)
    _ = (∫⁻ z, d x z * K x z ∂μ) + (∫⁻ z, K x z ∂μ) * B := by
      rw [lintegral_add_left (f := fun z => d x z * K x z)
        ((hdrow x).mul (hK x)), lintegral_mul_const _ (hK x)]
    _ ≤ A + B := by
      simpa only [one_mul] using add_le_add (hA x) (mul_le_mul_left (hmK x) B)

theorem lintegral_cost_semigroup_le_nat_mul
    {d : X → X → ℝ≥0∞} {K : ℝ → X → X → ℝ≥0∞}
    (hd : Measurable (Function.uncurry d))
    (htri : ∀ x z y, d x y ≤ d x z + d z y)
    (hK : ∀ t, 0 < t → Measurable (Function.uncurry (K t)))
    (hmass : ∀ t, 0 < t → ∀ x, ∫⁻ y, K t x y ∂μ ≤ 1)
    (hadd : ∀ s t, 0 < s → 0 < t → ∀ x y,
      K (s + t) x y = ∫⁻ z, K s x z * K t z y ∂μ)
    {C : ℝ≥0∞}
    (hsmall : ∀ t, 0 < t → t ≤ 1 → ∀ x, ∫⁻ y, d x y * K t x y ∂μ ≤ C)
    (N : ℕ) {t : ℝ} (ht : 0 < t) (hN : t ≤ N) (x : X) :
    ∫⁻ y, d x y * K t x y ∂μ ≤ N * C := by
  induction N generalizing t x with
  | zero => norm_num at hN; linarith
  | succ N ih =>
    by_cases ht1 : t ≤ 1
    · exact (hsmall t ht ht1 x).trans (by
        have h : (1 : ℝ≥0∞) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
        simpa only [one_mul] using mul_le_mul_left h C)
    · have hs : 0 < t - 1 := by linarith
      have hsN : t - 1 ≤ (N : ℝ) := by
        push_cast at hN
        linarith
      have heq : K t = K ((t - 1) + 1) := by congr 1; ring
      simp_rw [heq, hadd (t - 1) 1 hs zero_lt_one]
      have h := lintegral_cost_convolution_le (K := K (t - 1)) hd (hK 1 zero_lt_one) htri
        (fun z => (hK (t - 1) hs).comp measurable_prodMk_left)
        (hmass (t - 1) hs) (hmass 1 zero_lt_one)
        (fun z => ih hs hsN z) (hsmall 1 zero_lt_one le_rfl) x
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        Function.comp_apply, Function.uncurry_apply_pair] using h

theorem integrable_cost_semigroup_of_small_time
    {d : X → X → ℝ} {K : ℝ → X → X → ℝ}
    (hd : Measurable (Function.uncurry d)) (hd0 : ∀ x y, 0 ≤ d x y)
    (htri : ∀ x z y, d x y ≤ d x z + d z y)
    (hK : ∀ t, 0 < t → Measurable (Function.uncurry (K t)))
    (hK0 : ∀ t, 0 < t → ∀ x y, 0 ≤ K t x y)
    (hmass : ∀ t, 0 < t → ∀ x,
      Integrable (K t x) μ ∧ (∫ y, K t x y ∂μ) ≤ 1)
    (hadd : ∀ s t, 0 < s → 0 < t → ∀ x y,
      Integrable (fun z => K s x z * K t z y) μ ∧
        K (s + t) x y = ∫ z, K s x z * K t z y ∂μ)
    {C : ℝ}
    (hsmall : ∀ t, 0 < t → t ≤ 1 → ∀ x,
      Integrable (fun y => d x y * K t x y) μ ∧
        (∫ y, d x y * K t x y ∂μ) ≤ C)
    {t : ℝ} (ht : 0 < t) (x : X) :
    Integrable (fun y => d x y * K t x y) μ := by
  have hm : ∀ s, 0 < s → ∀ z, ∫⁻ y, ENNReal.ofReal (K s z y) ∂μ ≤ 1 := by
    intro s hs z
    rw [← ofReal_integral_eq_lintegral_ofReal (hmass s hs z).1
      (Filter.Eventually.of_forall (hK0 s hs z))]
    exact (ENNReal.ofReal_le_ofReal (hmass s hs z).2).trans_eq (by simp)
  have ha : ∀ s r, 0 < s → 0 < r → ∀ z y,
      ENNReal.ofReal (K (s + r) z y) =
        ∫⁻ w, ENNReal.ofReal (K s z w) * ENNReal.ofReal (K r w y) ∂μ := by
    intro s r hs hr z y
    rw [(hadd s r hs hr z y).2,
      ofReal_integral_eq_lintegral_ofReal (hadd s r hs hr z y).1
        (Filter.Eventually.of_forall fun w => mul_nonneg (hK0 s hs z w) (hK0 r hr w y))]
    simp_rw [ENNReal.ofReal_mul (hK0 s hs z _)]
  have hsm : ∀ s, 0 < s → s ≤ 1 → ∀ z,
      ∫⁻ y, ENNReal.ofReal (d z y) * ENNReal.ofReal (K s z y) ∂μ ≤
        ENNReal.ofReal C := by
    intro s hs hs1 z
    simp_rw [← ENNReal.ofReal_mul (hd0 z _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (hsmall s hs hs1 z).1
      (Filter.Eventually.of_forall fun y => mul_nonneg (hd0 z y) (hK0 s hs z y))]
    exact ENNReal.ofReal_le_ofReal (hsmall s hs hs1 z).2
  obtain ⟨N, hN⟩ := exists_nat_ge t
  have hbound := lintegral_cost_semigroup_le_nat_mul
    (μ := μ) (d := fun z y => ENNReal.ofReal (d z y))
    (K := fun s z y => ENNReal.ofReal (K s z y)) hd.ennreal_ofReal
    (fun z w y => (ENNReal.ofReal_le_ofReal (htri z w y)).trans
      ENNReal.ofReal_add_le)
    (fun s hs => (hK s hs).ennreal_ofReal) hm ha hsm N ht hN x
  have hnonneg : ∀ y, 0 ≤ d x y * K t x y :=
    fun y => mul_nonneg (hd0 x y) (hK0 t ht x y)
  refine ⟨((hd.comp measurable_prodMk_left).mul
    ((hK t ht).comp measurable_prodMk_left)).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)).mpr
  simp_rw [ENNReal.ofReal_mul (hd0 x _)]
  exact hbound.trans_lt (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)

end Poincare.MeasureTheory
