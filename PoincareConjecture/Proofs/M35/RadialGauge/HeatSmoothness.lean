import PoincareConjecture.Proofs.M35.RadialGauge.HeatWeight
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

universe u

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem heatAverage_integrable_of_bound
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : Continuous f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C)
    (t : ℝ) (x : V) :
    Integrable (fun z => f (x + Real.sqrt (2 * t) • z)) (stdGaussian V) := by
  exact (integrable_const C).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun z => hbound _))

theorem heatAverage_norm_le
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : Continuous f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C)
    (t : ℝ) (x : V) : ‖heatAverage t f x‖ ≤ C := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : V, C ∂stdGaussian V := integral_mono
      (heatAverage_integrable_of_bound hf hbound t x).norm (integrable_const C)
      (fun z => hbound _)
    _ = C := by simp

theorem heatAverage_continuous_of_bound
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : Continuous f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C)
    (t : ℝ) : Continuous (heatAverage t f) := by
  apply continuous_of_dominated
    (bound := fun _ : V => C)
  · intro x
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall (fun z => hbound _)
  · exact integrable_const C
  · exact Eventually.of_forall (fun z => hf.comp (by fun_prop))

theorem heatAverage_hasFDerivAt_of_bounds
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} {f' : V → V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (hdbound : ∀ x, ‖f' x‖ ≤ D)
    (t : ℝ) (x : V) :
    HasFDerivAt (heatAverage t f) (heatAverage t f' x) x := by
  change HasFDerivAt (fun y => ∫ z, f (y + Real.sqrt (2 * t) • z) ∂stdGaussian V) _ x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := univ) (F' := fun y z => f' (y + Real.sqrt (2 * t) • z))
    (bound := fun _ => D) (by simp)
  · exact Eventually.of_forall (fun y => (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact heatAverage_integrable_of_bound hf hbound t x
  · exact (hf'.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z y _ => hdbound _)
  · exact integrable_const D
  · refine Eventually.of_forall (fun z y _ => ?_)
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (hderiv _).comp y ((hasFDerivAt_id y).add_const (Real.sqrt (2 * t) • z))

private theorem derivative_bounds_shift
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : V → F}
    (hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ ≤ C := by
  intro k
  obtain ⟨C, hC⟩ := hbound (k + 1)
  exact ⟨C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using hC x⟩

private theorem heatAverage_contDiff_nat (k : ℕ)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : V → F}
    (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C)
    (t : ℝ) : ContDiff ℝ k (heatAverage t f) := by
  induction k generalizing F with
  | zero =>
      obtain ⟨C, hC⟩ := hbound 0
      apply contDiff_zero.mpr
      exact heatAverage_continuous_of_bound hf.continuous
        (fun x => by simpa only [norm_iteratedFDeriv_zero] using hC x) t
  | succ k ih =>
      have hdf := (contDiff_infty_iff_fderiv.mp hf).2
      obtain ⟨C, hC⟩ := hbound 0
      obtain ⟨D, hD⟩ := hbound 1
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨heatAverage t (fderiv ℝ f), ih hdf (derivative_bounds_shift hbound), ?_⟩
      intro x
      exact heatAverage_hasFDerivAt_of_bounds hf.continuous hdf.continuous
        (fun y => (hf.differentiable (by simp) y).hasFDerivAt)
        (fun y => by simpa only [norm_iteratedFDeriv_zero] using hC y)
        (fun y => by simpa only [norm_iteratedFDeriv_one] using hD y) t x

theorem heatAverage_contDiff
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : V → F}
    (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C)
    (t : ℝ) : ContDiff ℝ ∞ (heatAverage t f) :=
  contDiff_infty.mpr (fun k => heatAverage_contDiff_nat k hf hbound t)

theorem heatAverage_iteratedFDeriv_norm_le (k : ℕ)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : V → F}
    (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    {C : ℝ} (hk : ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    (t : ℝ) (x : V) : ‖iteratedFDeriv ℝ k (heatAverage t f) x‖ ≤ C := by
  induction k generalizing F with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact heatAverage_norm_le hf.continuous
        (fun y => by simpa only [norm_iteratedFDeriv_zero] using hk y) t x
  | succ k ih =>
      have hdf := (contDiff_infty_iff_fderiv.mp hf).2
      obtain ⟨B, hB⟩ := hbound 0
      obtain ⟨D, hD⟩ := hbound 1
      have hderiv : fderiv ℝ (heatAverage t f) = heatAverage t (fderiv ℝ f) := by
        funext y
        exact (heatAverage_hasFDerivAt_of_bounds hf.continuous hdf.continuous
          (fun z => (hf.differentiable (by simp) z).hasFDerivAt)
          (fun z => by simpa only [norm_iteratedFDeriv_zero] using hB z)
          (fun z => by simpa only [norm_iteratedFDeriv_one] using hD z) t y).fderiv
      rw [← norm_iteratedFDeriv_fderiv, hderiv]
      exact ih hdf (derivative_bounds_shift hbound)
        (fun y => by simpa only [norm_iteratedFDeriv_fderiv] using hk y)

end PoincareConjecture.M35.RadialGauge
