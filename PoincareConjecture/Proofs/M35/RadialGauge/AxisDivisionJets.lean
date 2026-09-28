import PoincareConjecture.Proofs.M35.Mathlib.SmoothAxisDivision
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial CoordinateExponential

theorem radialWeightedIntegral_hasDerivAt_scalar {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (r : ℝ) :
    HasDerivAt (radialWeightedIntegral k f)
      (radialWeightedIntegral (k + 1) (deriv f) r) r := by
  have hx : r ∈ Metric.ball (0 : ℝ) (‖r‖ + 1) := by simp
  have hd := hasFDerivAt_radialWeightedIntegral k
    (hf.of_le (by simp)).contDiffOn hx
  have hdf : Continuous (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2.continuous
  have hi : IntervalIntegrable
      (fun t : ℝ => t ^ (k + 1) • fderiv ℝ f (t * r)) volume 0 1 :=
    ((continuous_id.pow (k + 1)).smul
      (hdf.comp (continuous_id.mul_const r))).intervalIntegrable 0 1
  have heval := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).intervalIntegral_comp_comm hi
  have hid : (radialWeightedIntegral (k + 1) (fderiv ℝ f) r) 1 =
      radialWeightedIntegral (k + 1) (deriv f) r := by
    simpa only [radialWeightedIntegral, ContinuousLinearMap.apply_apply,
      smul_apply, smul_eq_mul, fderiv_apply_one_eq_deriv] using heval.symm
  exact hd.hasDerivAt.congr_deriv hid

theorem iteratedDeriv_radialWeightedIntegral_scalar {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (j k : ℕ) (r : ℝ) :
    iteratedDeriv j (radialWeightedIntegral k f) r =
      radialWeightedIntegral (k + j) (iteratedDeriv j f) r := by
  induction j generalizing f k with
  | zero => simp only [iteratedDeriv_zero, add_zero]
  | succ j ih =>
      have hd : deriv (radialWeightedIntegral k f) =
          radialWeightedIntegral (k + 1) (deriv f) :=
        funext (fun s => (radialWeightedIntegral_hasDerivAt_scalar hf k s).deriv)
      rw [iteratedDeriv_succ', hd, ih (contDiff_infty_iff_deriv.mp hf).2]
      simp only [iteratedDeriv_succ', Nat.add_assoc, Nat.add_comm 1 j]

theorem iteratedDeriv_axisDivision {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (r : ℝ) :
    iteratedDeriv j (axisDivision f) r =
      radialWeightedIntegral j (iteratedDeriv (j + 1) f) r := by
  change iteratedDeriv j (radialWeightedIntegral 0 (deriv f)) r = _
  rw [iteratedDeriv_radialWeightedIntegral_scalar
    (contDiff_infty_iff_deriv.mp hf).2]
  simp only [zero_add, iteratedDeriv_succ']

theorem axisDivision_jet_continuous {A : Type*} [TopologicalSpace A]
    {f : A → ℝ → ℝ} (hf : ∀ a, ContDiff ℝ ∞ (f a)) (j : ℕ)
    (hjoint : Continuous (fun p : A × ℝ => iteratedDeriv (j + 1) (f p.1) p.2)) :
    Continuous (fun p : A × ℝ => iteratedDeriv j (axisDivision (f p.1)) p.2) := by
  have harg : Continuous (fun p : (A × ℝ) × ℝ => (p.1.1, p.2 * p.1.2)) :=
    continuous_fst.fst.prodMk (continuous_snd.mul continuous_fst.snd)
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume)
    (f := fun (p : A × ℝ) t => t ^ j * iteratedDeriv (j + 1) (f p.1) (t * p.2))
    ((continuous_snd.pow j).mul (hjoint.comp harg)) (0 : ℝ) 1
  simpa only [iteratedDeriv_axisDivision (hf _), radialWeightedIntegral, smul_eq_mul,
    Function.uncurry] using h

end PoincareConjecture.M35.RadialGauge
