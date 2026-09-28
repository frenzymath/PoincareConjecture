import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Diffeomorphism.Perturbation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

open Set
open scoped ContDiff Manifold NNReal

namespace Poincare

theorem exists_diffeomorph_move_zero_in_unitBall
    {n : ℕ} {a : EuclideanSpace ℝ (Fin n)} (ha : ‖a‖ < 1) :
    ∃ (r : ℝ) (F : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞),
      0 < r ∧ r < 1 ∧ F 0 = a ∧ ∀ x, r ≤ ‖x‖ → F x = x := by
  let r₁ := (‖a‖ + 1) / 2
  let r₂ := (r₁ + 1) / 2
  have hr₁ : 0 < r₁ := by dsimp [r₁]; positivity
  have har₁ : ‖a‖ < r₁ := by dsimp [r₁]; linarith
  have hr₁₂ : r₁ < r₂ := by dsimp [r₁, r₂]; linarith
  have hr₂ : r₂ < 1 := by dsimp [r₁, r₂]; linarith
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨r₁, r₂, hr₁, hr₁₂⟩
  have hb : ContDiff ℝ ∞ (b : EuclideanSpace ℝ (Fin n) → ℝ) := b.contDiff
  obtain ⟨B, hB⟩ := (b.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv (by simp))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B * ‖a‖ + 1)
  have hNpos : 0 < (N : ℝ) := by nlinarith [norm_nonneg a]
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  let v := (N : ℝ)⁻¹ • a
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => x + b x • v
  have hf : ContDiff ℝ ∞ f := contDiff_id.add (b.contDiff.smul contDiff_const)
  have hv : B * ‖v‖ ≤ 1 / 2 := by
    rw [show ‖v‖ = ‖a‖ / N by simp [v, norm_smul, div_eq_mul_inv, mul_comm]]
    rw [← mul_div_assoc, div_le_iff₀ hNpos]
    linarith
  have hclose (x : EuclideanSpace ℝ (Fin n)) :
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤
        (1 / 2 : ℝ≥0) := by
    have hd := (hasFDerivAt_id x).add
      ((hb.differentiable (by simp) x).hasFDerivAt.smul_const v)
    change HasFDerivAt f
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) +
        (fderiv ℝ (b : EuclideanSpace ℝ (Fin n) → ℝ) x).smulRight v) x at hd
    rw [hd.fderiv, add_sub_cancel_left, ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg v)).trans hv
  obtain ⟨e, he, hs, hi⟩ :=
    Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id hf
      (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  let d : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞ :=
    ⟨e.toEquiv, hs.contMDiff, hi.contMDiff⟩
  have hd (x : EuclideanSpace ℝ (Fin n)) : d x = x + b x • v := congrFun he x
  let D : ℕ → Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞ :=
    Nat.rec (Diffeomorph.refl _ _ _) (fun _ F => F.trans d)
  have hstep (k : ℕ) (hk : k ≤ N) : D k 0 = ((k : ℝ) / N) • a := by
    induction k with
    | zero => simp [D]
    | succ k ih =>
      have hkN : k ≤ N := (Nat.le_succ k).trans hk
      have hnorm : ‖((k : ℝ) / N) • a‖ ≤ ‖a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left (norm_nonneg a)
          ((div_le_one hNpos).mpr (by exact_mod_cast hkN))
      have hb : b (((k : ℝ) / N) • a) = 1 :=
        b.one_of_mem_closedBall (by
          simpa [Metric.mem_closedBall, dist_zero_right] using (hnorm.trans har₁.le))
      change d (D k 0) = _
      rw [ih hkN, hd, hb, one_smul]
      change ((k : ℝ) / N) • a + (N : ℝ)⁻¹ • a = _
      rw [← add_smul]
      congr 1
      push_cast
      field_simp
  have hfix (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : r₂ ≤ ‖x‖) : D k x = x := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change d (D k x) = x
      rw [ih, hd, b.zero_of_le_dist (by simpa [dist_zero_right] using hx), zero_smul, add_zero]
  refine ⟨r₂, D N, hr₁.trans hr₁₂, hr₂, ?_, hfix N⟩
  simpa [hNne] using hstep N le_rfl

end Poincare
