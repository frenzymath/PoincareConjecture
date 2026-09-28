import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.RegularizedMinimum.Finite.Weights

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Poincare

private theorem left_factor_eq_zero (δ : ℝ) (hδ : 0 < δ) (x y : ℝ)
    (hx : regularizedMin δ hδ x y + 2 * δ < x) :
    (1 - deriv (regularizedAbs δ hδ) (x - y)) / 2 = 0 := by
  have hlow := min_sub_le_regularizedMin δ hδ x y
  have hgap : y + δ < x := by
    rcases le_total x y with h | h
    · rw [min_eq_left h] at hlow
      linarith
    · rw [min_eq_right h] at hlow
      linarith
  have hd : HasDerivAt (fun t => regularizedMin δ hδ t y) 0 x := by
    apply (hasDerivAt_const x y).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hgap] with t ht
    dsimp only [id_eq] at ht
    rw [regularizedMin_eq_min δ hδ (by
      rw [abs_of_nonneg (by linarith : 0 ≤ t - y)]
      linarith), min_eq_right (by linarith)]
  exact (hasDerivAt_regularizedMin_left δ hδ x y).unique hd

private theorem right_factor_eq_zero (δ : ℝ) (hδ : 0 < δ) (x y : ℝ)
    (hy : regularizedMin δ hδ x y + 2 * δ < y) :
    (1 + deriv (regularizedAbs δ hδ) (x - y)) / 2 = 0 := by
  have hlow := min_sub_le_regularizedMin δ hδ x y
  have hgap : x + δ < y := by
    rcases le_total x y with h | h
    · rw [min_eq_left h] at hlow
      linarith
    · rw [min_eq_right h] at hlow
      linarith
  have hd : HasDerivAt (regularizedMin δ hδ x) 0 y := by
    apply (hasDerivAt_const y x).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hgap] with t ht
    dsimp only [id_eq] at ht
    rw [regularizedMin_comm, regularizedMin_eq_min δ hδ (by
      rw [abs_of_nonneg (by linarith : 0 ≤ t - x)]
      linarith), min_eq_right (by linarith)]
  exact (hasDerivAt_regularizedMin_right δ hδ x y).unique hd

theorem finiteRegularizedMinWeight_eq_zero_of_value_gap
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (f : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hi : finiteRegularizedMin δ hδ n f + 2 * n * δ < f i) :
    finiteRegularizedMinWeight δ hδ n f i = 0 := by
  induction n with
  | zero =>
    simp only [finiteRegularizedMin, Nat.cast_zero, mul_zero, zero_mul, add_zero,
      Fin.fin_one_eq_zero i, lt_self_iff_false] at hi
  | succ n ih =>
    refine Fin.cases (fun hi => ?_) (fun i hi => ?_) i hi
    · apply left_factor_eq_zero
      have hn : 0 ≤ (n : ℝ) * δ := by positivity
      change regularizedMin δ hδ (f 0) (finiteRegularizedMin δ hδ n (Fin.tail f)) +
        2 * (n + 1 : ℕ) * δ < f 0 at hi
      push_cast at hi
      linarith
    · change ((1 + deriv (regularizedAbs δ hδ)
          (f 0 - finiteRegularizedMin δ hδ n (Fin.tail f))) / 2) *
        finiteRegularizedMinWeight δ hδ n (Fin.tail f) i = 0
      by_cases ht : finiteRegularizedMin δ hδ (n + 1) f + 2 * δ <
          finiteRegularizedMin δ hδ n (Fin.tail f)
      · rw [right_factor_eq_zero δ hδ _ _ ht, zero_mul]
      · rw [ih (Fin.tail f) i (by
          push_cast at hi
          dsimp only [Fin.tail]
          linarith), mul_zero]

theorem finiteRegularizedMinWeight_eq_zero_of_iInf_gap
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (f : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hi : (⨅ j, f j) + 2 * n * δ < f i) :
    finiteRegularizedMinWeight δ hδ n f i = 0 := by
  apply finiteRegularizedMinWeight_eq_zero_of_value_gap
  have h := finiteRegularizedMin_le_iInf δ hδ n f
  linarith

theorem hasDerivAt_finiteRegularizedMin_update
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (t : ℝ) :
    HasDerivAt (fun s => finiteRegularizedMin δ hδ n (Function.update f i s))
      (finiteRegularizedMinWeight δ hδ n (Function.update f i t) i) t := by
  rw [finiteRegularizedMinWeight_eq_fderiv]
  exact ((contDiff_finiteRegularizedMin δ hδ n).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
    t (hasDerivAt_update f i t)

theorem finiteRegularizedMin_update_eq
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (f : Fin (n + 1) → ℝ) (i j : Fin (n + 1))
    (hji : j ≠ i) (t : ℝ)
    (hi : f j + 2 * n * δ < f i) (ht : f j + 2 * n * δ < t) :
    finiteRegularizedMin δ hδ n (Function.update f i t) = finiteRegularizedMin δ hδ n f := by
  have hconst := (isOpen_Ioi : IsOpen (Ioi (f j + 2 * n * δ))).is_const_of_deriv_eq_zero
    isPreconnected_Ioi
    (fun s _ => (hasDerivAt_finiteRegularizedMin_update δ hδ n f i s).differentiableAt.differentiableWithinAt)
    (fun s hs => ?_) ht hi
  · simpa only [Function.update_eq_self] using hconst
  · rw [(hasDerivAt_finiteRegularizedMin_update δ hδ n f i s).deriv]
    apply finiteRegularizedMinWeight_eq_zero_of_value_gap
    have hle := finiteRegularizedMin_le δ hδ n (Function.update f i s) j
    simp only [Function.update_of_ne hji] at hle
    simp only [Function.update_self]
    change f j + 2 * n * δ < s at hs
    linarith

theorem finiteRegularizedMin_update_eventuallyEq
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (f : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hi : (⨅ j, f j) + 2 * n * δ < f i) :
    (fun g => finiteRegularizedMin δ hδ n (Function.update g i (f i))) =ᶠ[𝓝 f]
      finiteRegularizedMin δ hδ n := by
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := f)
  have hgap : f j + 2 * n * δ < f i := by simpa only [hj] using hi
  have hji : j ≠ i := by
    intro h
    subst j
    have hn : 0 ≤ 2 * (n : ℝ) * δ := by positivity
    linarith
  have hc : Continuous (fun g : Fin (n + 1) → ℝ => g j + 2 * n * δ) := by fun_prop
  have hci : Continuous (fun g : Fin (n + 1) → ℝ => g i) := continuous_apply i
  have hfirst : ∀ᶠ g : Fin (n + 1) → ℝ in 𝓝 f, g j + 2 * n * δ < g i :=
    hc.continuousAt.eventually_lt hci.continuousAt hgap
  have hsecond : ∀ᶠ g : Fin (n + 1) → ℝ in 𝓝 f, g j + 2 * n * δ < f i :=
    hc.continuousAt.eventually_lt continuousAt_const hgap
  filter_upwards [hfirst, hsecond] with g hgi hgt
  exact finiteRegularizedMin_update_eq δ hδ n g i j hji (f i) hgi hgt

end Poincare
