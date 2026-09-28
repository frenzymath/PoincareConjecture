import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set MeasureTheory Filter

namespace Poincare.Analysis.Heat

theorem summable_gaussian_mul_exp_nat {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Summable (fun n : ℕ ↦ Real.exp (-a * (n : ℝ) ^ 2 + c * ((n : ℝ) + 1))) := by
  apply (Real.summable_exp_neg_nat.mul_left (Real.exp c)).of_norm_bounded_eventually_nat
  obtain ⟨N, hN⟩ := exists_nat_ge ((c + 1) / a)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hlarge : (c + 1) / a ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have hlarge' : c + 1 ≤ a * (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hlarge
  have hprod := mul_nonneg (sub_nonneg.mpr hlarge') (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem integrable_gaussian_weight_of_ball_integral_le_exp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {r q : X → ℝ}
    (hr : Measurable r) (hq : AEStronglyMeasurable q μ)
    (hr0 : ∀ x, 0 ≤ r x) (hq0 : ∀ x, 0 ≤ q x)
    {a C c : ℝ} (ha : 0 < a)
    (hqi : ∀ n : ℕ, IntegrableOn q {x | r x < (n : ℝ) + 1} μ)
    (hbound : ∀ n : ℕ,
      (∫ x in {x | r x < (n : ℝ) + 1}, q x ∂μ) ≤
        C * Real.exp (c * ((n : ℝ) + 1))) :
    Integrable (fun x ↦ Real.exp (-a * r x ^ 2) * q x) μ := by
  let s : ℕ → Set X := fun n ↦ {x | (n : ℝ) ≤ r x ∧ r x < (n : ℝ) + 1}
  let f : X → ℝ := fun x ↦ Real.exp (-a * r x ^ 2) * q x
  have hs (n : ℕ) : MeasurableSet (s n) :=
    (measurableSet_le measurable_const hr).inter (measurableSet_lt hr measurable_const)
  have hsub (n : ℕ) : s n ⊆ {x | r x < (n : ℝ) + 1} := fun _ hx ↦ hx.2
  have hfm : AEStronglyMeasurable f μ :=
    ((hr.pow_const 2).const_mul (-a)).exp.aestronglyMeasurable.mul hq
  have hf0 (x : X) : 0 ≤ f x := mul_nonneg (Real.exp_nonneg _) (hq0 x)
  have hfi (n : ℕ) : IntegrableOn f (s n) μ := by
    apply ((hqi n).mono_set (hsub n)).mono' hfm.restrict
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hf0 x)]
    exact mul_le_of_le_one_left (hq0 x) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (r x)]))
  have hs_bound (n : ℕ) :
      (∫ x in s n, ‖f x‖ ∂μ) ≤
        C * Real.exp (-a * (n : ℝ) ^ 2 + c * ((n : ℝ) + 1)) := by
    simp_rw [Real.norm_of_nonneg (hf0 _)]
    calc
      (∫ x in s n, f x ∂μ) ≤
          ∫ x in s n, Real.exp (-a * (n : ℝ) ^ 2) * q x ∂μ := by
        apply integral_mono_ae (hfi n) (((hqi n).mono_set (hsub n)).const_mul _)
        filter_upwards [ae_restrict_mem (hs n)] with x hx
        apply mul_le_mul_of_nonneg_right _ (hq0 x)
        apply Real.exp_le_exp.mpr
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        have hsq : (n : ℝ) ^ 2 ≤ r x ^ 2 := by nlinarith [hx.1, hr0 x]
        exact mul_le_mul_of_nonpos_left hsq (by linarith)
      _ = Real.exp (-a * (n : ℝ) ^ 2) * (∫ x in s n, q x ∂μ) :=
        integral_const_mul _ _
      _ ≤ Real.exp (-a * (n : ℝ) ^ 2) *
          (∫ x in {x | r x < (n : ℝ) + 1}, q x ∂μ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact setIntegral_mono_set (hqi n) (ae_of_all _ hq0) (ae_of_all _ (hsub n))
      _ ≤ Real.exp (-a * (n : ℝ) ^ 2) * (C * Real.exp (c * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (hbound n) (Real.exp_nonneg _)
      _ = C * Real.exp (-a * (n : ℝ) ^ 2 + c * ((n : ℝ) + 1)) := by
        rw [Real.exp_add]
        ring
  have hsum : Summable (fun n : ℕ ↦ ∫ x in s n, ‖f x‖ ∂μ) :=
    ((summable_gaussian_mul_exp_nat ha c).mul_left C).of_nonneg_of_le
      (fun _ ↦ integral_nonneg (fun _ ↦ norm_nonneg _)) hs_bound
  have hcover : (⋃ n, s n) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨⌊r x⌋₊, Nat.floor_le (hr0 x), Nat.lt_floor_add_one (r x)⟩
  simpa only [hcover, integrableOn_univ] using
    integrableOn_iUnion_of_summable_integral_norm hfi hsum

theorem cutoff_energy_growth_le_exp {R A b C₀ V c : ℝ}
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hb : 0 ≤ b) (hC₀ : 0 ≤ C₀) (hV : 0 ≤ V) :
    (5 * R + A) ^ 2 * (1 + 4 * b * (C₀ / R) ^ 2) * V * Real.exp (c * (5 * R)) ≤
      ((5 + A) ^ 2 * (1 + 4 * b * C₀ ^ 2) * V) * Real.exp ((2 + 5 * c) * R) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlinear : 5 * R + A ≤ (5 + A) * Real.exp R := by
    have hRexp : R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
    calc
      5 * R + A ≤ (5 + A) * R := by nlinarith
      _ ≤ (5 + A) * Real.exp R :=
        mul_le_mul_of_nonneg_left hRexp (by positivity)
  have hpoly : (5 * R + A) ^ 2 ≤ (5 + A) ^ 2 * Real.exp (2 * R) := by
    calc
      (5 * R + A) ^ 2 ≤ ((5 + A) * Real.exp R) ^ 2 := by
        nlinarith [Real.exp_pos R]
      _ = (5 + A) ^ 2 * Real.exp (2 * R) := by
        rw [show 2 * R = R + R by ring, Real.exp_add]
        ring
  have hquot : C₀ / R ≤ C₀ := (div_le_iff₀ hR0).mpr (by nlinarith)
  have hquot0 : 0 ≤ C₀ / R := div_nonneg hC₀ hR0.le
  have hfactor : 1 + 4 * b * (C₀ / R) ^ 2 ≤ 1 + 4 * b * C₀ ^ 2 := by
    have hsq : (C₀ / R) ^ 2 ≤ C₀ ^ 2 := by nlinarith
    nlinarith
  calc
    (5 * R + A) ^ 2 * (1 + 4 * b * (C₀ / R) ^ 2) * V * Real.exp (c * (5 * R)) ≤
        ((5 + A) ^ 2 * Real.exp (2 * R)) * (1 + 4 * b * C₀ ^ 2) * V *
          Real.exp (c * (5 * R)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hV
      exact mul_le_mul hpoly hfactor (by positivity) (by positivity)
    _ = ((5 + A) ^ 2 * (1 + 4 * b * C₀ ^ 2) * V) * Real.exp ((2 + 5 * c) * R) := by
      rw [show (2 + 5 * c) * R = 2 * R + c * (5 * R) by ring, Real.exp_add]
      ring

end Poincare.Analysis.Heat
