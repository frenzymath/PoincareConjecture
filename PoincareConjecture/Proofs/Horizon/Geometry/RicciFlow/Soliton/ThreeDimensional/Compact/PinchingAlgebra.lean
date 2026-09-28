import Mathlib.Analysis.SpecialFunctions.Pow.Deriv















set_option autoImplicit false

noncomputable section

namespace Poincare.ThreeDimensionalRicciPinching

def scalar (a b c : ℝ) : ℝ := a + b + c

def normSq (a b c : ℝ) : ℝ := a ^ 2 + b ^ 2 + c ^ 2

def traceFreeNormSq (a b c : ℝ) : ℝ :=
  normSq a b c - scalar a b c ^ 2 / 3

def quartic (a b c : ℝ) : ℝ :=
  2 * normSq a b c ^ 2 + scalar a b c ^ 4 -
    5 * scalar a b c ^ 2 * normSq a b c +
    4 * scalar a b c * (a ^ 3 + b ^ 3 + c ^ 3)

theorem traceFreeNormSq_eq_gaps (a b c : ℝ) :
    traceFreeNormSq a b c =
      ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) / 3 := by
  unfold traceFreeNormSq normSq scalar
  ring

theorem traceFreeNormSq_nonneg (a b c : ℝ) : 0 ≤ traceFreeNormSq a b c := by
  rw [traceFreeNormSq_eq_gaps]
  positivity

theorem traceFreeNormSq_eq_zero_iff (a b c : ℝ) :
    traceFreeNormSq a b c = 0 ↔ a = b ∧ b = c := by
  rw [traceFreeNormSq_eq_gaps]
  constructor
  · intro h
    have hab : (a - b) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - c)]
    have hbc : (b - c) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c)]
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    simp

theorem quartic_eq_gaps (a b c : ℝ) :
    quartic a b c =
      (a - b) ^ 2 * (a + b - c) ^ 2 +
        (a - c) ^ 2 * (a + c - b) ^ 2 +
        (b - c) ^ 2 * (b + c - a) ^ 2 := by
  unfold quartic normSq scalar
  ring

theorem quartic_nonneg (a b c : ℝ) : 0 ≤ quartic a b c := by
  rw [quartic_eq_gaps]
  positivity



theorem quartic_ge_least_sq_mul_traceFree
    {a b c : ℝ} (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 ≤ c) :
    3 * c ^ 2 * traceFreeNormSq a b c ≤ quartic a b c := by
  have hid : quartic a b c - 3 * c ^ 2 * traceFreeNormSq a b c =
      2 * (a - b) ^ 2 * ((a - b) ^ 2 + 3 * (a - b) * (b - c) +
        2 * (a - b) * c + 3 * (b - c) ^ 2 + 4 * (b - c) * c) := by
    unfold quartic traceFreeNormSq normSq scalar
    ring
  have hnonneg : 0 ≤ 2 * (a - b) ^ 2 *
      ((a - b) ^ 2 + 3 * (a - b) * (b - c) +
        2 * (a - b) * c + 3 * (b - c) ^ 2 + 4 * (b - c) * c) := by
    have ha : 0 ≤ a - b := sub_nonneg.mpr hab
    have hb : 0 ≤ b - c := sub_nonneg.mpr hbc
    positivity
  linarith

theorem quartic_ge_scalar_sq_mul_traceFree
    {a b c δ : ℝ} (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hpinch : δ * scalar a b c ≤ c) :
    3 * δ ^ 2 * scalar a b c ^ 2 * traceFreeNormSq a b c ≤ quartic a b c := by
  have hR : 0 ≤ scalar a b c := by
    unfold scalar
    linarith
  have hsq : (δ * scalar a b c) ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hδ hR) hpinch 2
  have hmul := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (traceFreeNormSq_nonneg a b c))
  have hbound := quartic_ge_least_sq_mul_traceFree hab hbc hc
  nlinarith only [hmul, hbound]

theorem quartic_ge_normSq_mul_traceFree
    {a b c δ : ℝ} (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hpinch : δ * scalar a b c ≤ c) :
    2 * δ ^ 2 * normSq a b c * traceFreeNormSq a b c ≤ quartic a b c := by
  have hnorm : normSq a b c ≤ scalar a b c ^ 2 := by
    have hb := hc.trans hbc
    have ha := hb.trans hab
    unfold normSq scalar
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  have hmul := mul_le_mul_of_nonneg_right hnorm
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg δ))
      (traceFreeNormSq_nonneg a b c))
  have hextra : 0 ≤ δ ^ 2 * scalar a b c ^ 2 * traceFreeNormSq a b c := by
    exact mul_nonneg (mul_nonneg (sq_nonneg δ) (sq_nonneg _))
      (traceFreeNormSq_nonneg a b c)
  have hbound := quartic_ge_scalar_sq_mul_traceFree hab hbc hc hδ hpinch
  nlinarith only [hmul, hextra, hbound]

theorem weighted_reaction_numerator_nonpos
    {a b c δ ε : ℝ} (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hpinch : δ * scalar a b c ≤ c) (hε : ε ≤ 2 * δ ^ 2) :
    ε * normSq a b c * traceFreeNormSq a b c - quartic a b c ≤ 0 := by
  have hprod : 0 ≤ normSq a b c * traceFreeNormSq a b c := by
    apply mul_nonneg _ (traceFreeNormSq_nonneg a b c)
    unfold normSq
    positivity
  have hcoef := mul_le_mul_of_nonneg_right hε hprod
  have hbound := quartic_ge_normSq_mul_traceFree hab hbc hc hδ hpinch
  nlinarith only [hcoef, hbound]

theorem quartic_eq_contracted_polynomial (a b c : ℝ) :
    quartic a b c = 2 * normSq a b c ^ 2 - 2 * scalar a b c *
      ((5 / 2 : ℝ) * scalar a b c * normSq a b c -
        (1 / 2 : ℝ) * scalar a b c ^ 3 - 2 * (a ^ 3 + b ^ 3 + c ^ 3)) := by
  unfold quartic
  ring

end Poincare.ThreeDimensionalRicciPinching
