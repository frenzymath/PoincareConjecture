import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

theorem integral_mul_trace_fderiv {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {u : E → ℝ} {V : E → E}
    (hu : ∀ x ∈ tsupport V, DifferentiableAt ℝ u x)
    (hV : ∀ x ∈ tsupport u, DifferentiableAt ℝ V x)
    (hleft : ∀ i, Integrable (fun x ↦ fderiv ℝ u x (b i) * inner ℝ (b i) (V x)) μ)
    (hright : ∀ i, Integrable (fun x ↦ u x * inner ℝ (b i) (fderiv ℝ V x (b i))) μ)
    (hprod : ∀ i, Integrable (fun x ↦ u x * inner ℝ (b i) (V x)) μ) :
    Integrable (fun x ↦ u x * LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap) μ ∧
      Integrable (fun x ↦ fderiv ℝ u x (V x)) μ ∧
      (∫ x, u x * LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap ∂μ) =
        -(∫ x, fderiv ℝ u x (V x) ∂μ) := by
  classical
  have hpair (x : E) : fderiv ℝ u x (V x) =
      ∑ i, fderiv ℝ u x (b i) * inner ℝ (b i) (V x) := by
    nth_rw 1 [← b.sum_repr' (V x)]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have htrace (x : E) : u x * LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap =
      ∑ i, u x * inner ℝ (b i) (fderiv ℝ V x (b i)) := by
    rw [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum]
    rfl
  have hcoordinate (i : ι) (x : E) :
      u x * fderiv ℝ (fun y ↦ inner ℝ (b i) (V y)) x (b i) =
        u x * inner ℝ (b i) (fderiv ℝ V x (b i)) := by
    by_cases hx : u x = 0
    · simp only [hx, zero_mul]
    · rw [fderiv_inner_apply ℝ (differentiableAt_const (b i)) (hV x (subset_closure hx))]
      have hc : fderiv ℝ (fun _ : E ↦ b i) x = 0 := fderiv_const_apply (b i)
      simp only [hc, zero_apply, inner_zero_left, add_zero]
  have hparts (i : ι) :
      (∫ x, u x * inner ℝ (b i) (fderiv ℝ V x (b i)) ∂μ) =
        -(∫ x, fderiv ℝ u x (b i) * inner ℝ (b i) (V x) ∂μ) := by
    have hsupp : tsupport (fun x ↦ inner ℝ (b i) (V x)) ⊆ tsupport V := by
      apply closure_mono
      intro x hx
      change V x ≠ 0
      intro hz
      exact hx (by simp only [hz, inner_zero_right])
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (v := b i) (hleft i) (by simpa only [hcoordinate] using hright i) (hprod i)
      (fun x hx ↦ hu x (hsupp hx))
      (fun x hx ↦ (differentiableAt_const (b i)).inner ℝ (hV x hx))
    simpa only [hcoordinate] using h
  have hrightSum := integrable_finsetSum Finset.univ (fun i _ ↦ hright i)
  have hleftSum := integrable_finsetSum Finset.univ (fun i _ ↦ hleft i)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [← htrace] using hrightSum
  · simpa only [← hpair] using hleftSum
  · simp_rw [htrace, hpair]
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hright i),
      integral_finsetSum Finset.univ (fun i _ ↦ hleft i)]
    simp_rw [hparts]
    exact Finset.sum_neg_distrib _

end PoincareConjecture.M10
