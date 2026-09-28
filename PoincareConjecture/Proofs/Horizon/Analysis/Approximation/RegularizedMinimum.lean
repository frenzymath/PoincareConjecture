import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.RegularizedMinimum.AbsoluteValue








set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare


noncomputable def regularizedMin (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) : ℝ :=
  (x + y - regularizedAbs δ hδ (x - y)) / 2

theorem contDiff_regularizedMin (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => regularizedMin δ hδ p.1 p.2) :=
  ((contDiff_fst.add contDiff_snd).sub
    ((contDiff_regularizedAbs δ hδ).comp (contDiff_fst.sub contDiff_snd))).div_const 2

theorem regularizedMin_comm (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    regularizedMin δ hδ x y = regularizedMin δ hδ y x := by
  unfold regularizedMin
  rw [show y - x = -(x - y) by ring, regularizedAbs_neg]
  ring

theorem regularizedMin_add (δ : ℝ) (hδ : 0 < δ) (x y t : ℝ) :
    regularizedMin δ hδ (x + t) (y + t) = regularizedMin δ hδ x y + t := by
  unfold regularizedMin
  rw [show x + t - (y + t) = x - y by ring]
  ring

private theorem min_formula (x y : ℝ) : min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem regularizedMin_le_min (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    regularizedMin δ hδ x y ≤ min x y := by
  rw [min_formula]
  unfold regularizedMin
  linarith [abs_le_regularizedAbs δ hδ (x - y)]

theorem min_sub_le_regularizedMin (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    min x y - δ / 2 ≤ regularizedMin δ hδ x y := by
  rw [min_formula]
  unfold regularizedMin
  linarith [regularizedAbs_le_abs_add δ hδ (x - y)]

theorem regularizedMin_eq_min (δ : ℝ) (hδ : 0 < δ) {x y : ℝ}
    (hxy : δ ≤ |x - y|) : regularizedMin δ hδ x y = min x y := by
  rw [regularizedMin, regularizedAbs_eq_abs δ hδ hxy, min_formula]

theorem hasDerivAt_regularizedMin_left (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    HasDerivAt (fun t => regularizedMin δ hδ t y)
      ((1 - deriv (regularizedAbs δ hδ) (x - y)) / 2) x := by
  have ha := ((contDiff_regularizedAbs δ hδ).differentiable (by simp) (x - y)).hasDerivAt
  simpa +instances only [regularizedMin, Function.comp_def, Pi.sub_apply, id_eq, mul_one] using
    (((hasDerivAt_id x).add_const y).sub
      (ha.comp x ((hasDerivAt_id x).sub_const y))).div_const 2

theorem hasDerivAt_regularizedMin_right (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    HasDerivAt (regularizedMin δ hδ x)
      ((1 + deriv (regularizedAbs δ hδ) (x - y)) / 2) y := by
  have ha := ((contDiff_regularizedAbs δ hδ).differentiable (by simp) (x - y)).hasDerivAt
  change HasDerivAt (fun t => (x + t - regularizedAbs δ hδ (x - t)) / 2) _ y
  simpa +instances only [regularizedMin, Function.comp_def, Pi.sub_apply, id_eq,
    mul_neg, mul_one, sub_neg_eq_add] using
    (((hasDerivAt_id y).const_add x).sub
      (ha.comp y ((hasDerivAt_id y).const_sub x))).div_const 2

theorem regularizedMin_partial_derivatives (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    0 ≤ deriv (fun t => regularizedMin δ hδ t y) x ∧
    0 ≤ deriv (regularizedMin δ hδ x) y ∧
    deriv (fun t => regularizedMin δ hδ t y) x +
      deriv (regularizedMin δ hδ x) y = 1 := by
  rw [(hasDerivAt_regularizedMin_left δ hδ x y).deriv,
    (hasDerivAt_regularizedMin_right δ hδ x y).deriv]
  have h := abs_le.mp (abs_deriv_regularizedAbs_le_one δ hδ (x - y))
  exact ⟨by linarith, by linarith, by ring⟩

theorem monotone_regularizedMin_left (δ : ℝ) (hδ : 0 < δ) (y : ℝ) :
    Monotone (fun x => regularizedMin δ hδ x y) :=
  monotone_of_deriv_nonneg
    (fun x => (hasDerivAt_regularizedMin_left δ hδ x y).differentiableAt)
    (fun x => (regularizedMin_partial_derivatives δ hδ x y).1)

theorem monotone_regularizedMin_right (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    Monotone (regularizedMin δ hδ x) :=
  monotone_of_deriv_nonneg
    (fun y => (hasDerivAt_regularizedMin_right δ hδ x y).differentiableAt)
    (fun y => (regularizedMin_partial_derivatives δ hδ x y).2.1)

theorem concaveOn_regularizedMin (δ : ℝ) (hδ : 0 < δ) :
    ConcaveOn ℝ univ (fun p : ℝ × ℝ => regularizedMin δ hδ p.1 p.2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (convexOn_regularizedAbs δ hδ).2
    (mem_univ (x.1 - x.2)) (mem_univ (y.1 - y.2)) ha hb hab
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul, regularizedMin] at h ⊢
  rw [show a * x.1 + b * y.1 - (a * x.2 + b * y.2) =
    a * (x.1 - x.2) + b * (y.1 - y.2) by ring]
  nlinarith

end Poincare
