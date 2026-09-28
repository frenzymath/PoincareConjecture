import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open scoped ContDiff Topology

namespace PoincareConjecture.M36

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem comparison_iteratedFDeriv_comp_equiv (L : E ≃L[ℝ] E)
    (f : E → F) (x : E) (j : ℕ) :
    iteratedFDeriv ℝ j (f ∘ L) x =
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap
        (fun _ => L.toContinuousLinearMap) := by
  have h := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (Set.mem_univ (L x)) j
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using h

theorem norm_iteratedFDeriv_comp_dilation (f : E → F) {a : ℝ}
    (ha : a ≠ 0) (x : E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => f (a • y)) x‖ ≤
      |a| ^ j * ‖iteratedFDeriv ℝ j f (a • x)‖ := by
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  have hL (y : E) : L y = a • y := rfl
  have hnorm : ‖L.toContinuousLinearMap‖ ≤ |a| := by
    apply L.toContinuousLinearMap.opNorm_le_bound (abs_nonneg a)
    intro y
    change ‖a • y‖ ≤ |a| * ‖y‖
    rw [norm_smul, Real.norm_eq_abs]
  change ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ _
  rw [comparison_iteratedFDeriv_comp_equiv]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ‖L.toContinuousLinearMap‖ ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ j f (L x)).norm_compContinuousLinearMap_le
          (fun _ => L.toContinuousLinearMap)
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * |a| ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm j) (norm_nonneg _)
    _ = _ := by rw [hL, mul_comm]

theorem norm_iteratedFDeriv_dilation_at {f : E → F} {a b : ℝ} {x : E} {j m : ℕ}
    (ha : 0 < a) (ha2 : a ≤ 2) (hf : ContDiffAt ℝ ∞ f (a • x))
    (hb : 0 ≤ b) (hjet : ‖iteratedFDeriv ℝ j f (a • x)‖ ≤ b) (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (fun y => a ^ 2 • f (a • y)) x‖ ≤ (2 : ℝ) ^ (m + 2) * b := by
  have hcomp : ContDiffAt ℝ ∞ (fun y => f (a • y)) x :=
    hf.comp x (contDiffAt_id.const_smul a)
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  calc
    _ ≤ a ^ 2 * (|a| ^ j * ‖iteratedFDeriv ℝ j f (a • x)‖) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_comp_dilation f ha.ne' x j) (sq_nonneg a)
    _ ≤ a ^ 2 * (a ^ j * b) := by
      rw [abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjet (pow_nonneg ha.le _)) (sq_nonneg a)
    _ = a ^ (j + 2) * b := by rw [pow_add]; ring
    _ ≤ (2 : ℝ) ^ (j + 2) * b :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le ha2 _) hb
    _ ≤ (2 : ℝ) ^ (m + 2) * b := by gcongr; norm_num

end PoincareConjecture.M36
