import PoincareConjecture.Proofs.M35.Mathlib.SmoothEvenRadial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inner_jet_bound (j : ℕ) {R : ℝ} (hR : 0 ≤ R) (x : E) (hx : ‖x‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) x‖ ≤ R + 1 := by
  cases j with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      have h := ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (norm_innerSL_le ℝ) (norm_nonneg x))
      simp only [one_mul] at h
      linarith
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv]
      have hd : fderiv ℝ (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) =
          fun _ => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) :=
        funext (fun _ => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.fderiv)
      rw [hd]
      cases j with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          exact (norm_innerSL_le ℝ).trans (by linarith)
      | succ j =>
          simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
          positivity

private theorem divided_gradient_jets_bounded {A : Type*} {f : A → ℝ → ℝ}
    {R : ℝ} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, |r| ≤ R →
      |iteratedDeriv j (f a) r| ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, |r| ≤ R →
      |iteratedDeriv j (axisDivision (deriv (f a))) r| ≤ C := by
  intro j
  obtain ⟨C, hC, hCb⟩ := hb (j + 2)
  refine ⟨C, hC, ?_⟩
  intro a r hr
  have hdf := (contDiff_infty_iff_deriv.mp (hf a)).2
  have hddf := (contDiff_infty_iff_deriv.mp hdf).2
  have hx : r ∈ Metric.ball (0 : ℝ) (‖r‖ + 1) := by simp
  have h := norm_iteratedFDeriv_radialWeightedIntegral_le j 0 hddf.contDiffOn hx hC ?_
  · change ‖iteratedFDeriv ℝ j (axisDivision (deriv (f a))) r‖ ≤ _ at h
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
    apply h.trans
    exact div_le_self hC (by have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j; linarith)
  · intro t ht
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    have htr : |t * r| ≤ R := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg r)).trans
        (by simpa only [one_mul] using hr)
    simpa only [iteratedDeriv_succ', smul_eq_mul] using hCb a (t * r) htr

theorem even_radial_compact_jets_bounded {A : Type*} {f : A → ℝ → ℝ}
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (he : ∀ a, Function.Even (f a))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, |r| ≤ R →
      |iteratedDeriv j (f a) r| ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ j (fun y : E => f a ‖y‖) x‖ ≤ C := by
  classical
  suffices h : ∀ j : ℕ, ∀ f : A → ℝ → ℝ,
      (∀ a, ContDiff ℝ ∞ (f a)) → (∀ a, Function.Even (f a)) →
      (∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, |r| ≤ R → |iteratedDeriv i (f a) r| ≤ C) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E, ‖x‖ ≤ R →
        ‖iteratedFDeriv ℝ j (fun y : E => f a ‖y‖) x‖ ≤ C from
    fun j => h j f hf he hb
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro f hf he hb
      cases j with
      | zero =>
          obtain ⟨C, hC, hCb⟩ := hb 0
          refine ⟨C, hC, ?_⟩
          intro a x hx
          simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, iteratedDeriv_zero,
            abs_norm] using hCb a ‖x‖ (by simpa only [abs_norm] using hx)
      | succ k =>
          let q (a : A) := axisDivision (deriv (f a))
          have hq (a : A) : ContDiff ℝ ∞ (q a) :=
            axisDivision_contDiff (contDiff_infty_iff_deriv.mp (hf a)).2
          have hqe (a : A) : Function.Even (q a) := axisDivision_deriv_even (hf a) (he a)
          have hqb := divided_gradient_jets_bounded hf hb
          have hU (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
              (i ≤ k → ∀ a, ∀ x : E, ‖x‖ ≤ R →
                ‖iteratedFDeriv ℝ i (fun y : E => q a ‖y‖) x‖ ≤ C) := by
            by_cases hi : i ≤ k
            · obtain ⟨C, hC, hCb⟩ := ih i (by omega) q hq hqe hqb
              exact ⟨C, hC, fun _ => hCb⟩
            · exact ⟨0, le_rfl, fun h => (hi h).elim⟩
          choose U hU0 hUb using hU
          let C := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * U i * (R + 1)
          refine ⟨C, Finset.sum_nonneg (fun i _ =>
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hU0 i)) (by linarith)), ?_⟩
          intro a x hx
          rw [← norm_iteratedFDeriv_fderiv]
          have hd : fderiv ℝ (fun y : E => f a ‖y‖) =
              fun y => q a ‖y‖ • innerSL ℝ y :=
            funext (fun y => (hasFDerivAt_even_norm (hf a) (he a) y).fderiv)
          rw [hd]
          apply (norm_iteratedFDeriv_smul_le (contDiff_even_norm (hq a) (hqe a))
            (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).contDiff x
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).trans
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left
              (hUb i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi) a x hx)
              (Nat.cast_nonneg _))
            (inner_jet_bound (k - i) hR x hx) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (hU0 i))

end PoincareConjecture.M35.RadialGauge
