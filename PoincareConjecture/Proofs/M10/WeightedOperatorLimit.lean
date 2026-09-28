import PoincareConjecture.Proofs.M10.WeightedOperatorFormula









set_option autoImplicit false

open Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem trace_weightedMetricDual_tendsto {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ u : E → ℝ}
    {f : ℕ → E → ℝ} {x : E} (hB : ContDiffAt ℝ 1 B x) (hρ : DifferentiableAt ℝ ρ x)
    (hu : ContDiffAt ℝ 2 u x) (hf : ∀ j, ContDiffAt ℝ 2 (f j) x)
    (hi : (B x).IsInvertible) (C : E ≃L[ℝ] E)
    (hC : ∀ v w, B x (C v) (C w) = inner ℝ v w)
    (hfirst : Tendsto (fun j ↦ fderiv ℝ (f j) x) atTop (𝓝 (fderiv ℝ u x)))
    (hsecond : Tendsto (fun j ↦ fderiv ℝ (fderiv ℝ (f j)) x)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ u) x))) :
    Tendsto (fun j ↦ LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ (f j)) x).toLinearMap) atTop
      (𝓝 (LinearMap.trace ℝ E (fderiv ℝ (weightedMetricDual B ρ u) x).toLinearMap)) := by
  have ha := ((B x).inverse.continuous.tendsto _).comp hfirst
  have hterm (i : ι) :=
    (((ContinuousLinearMap.apply ℝ ℝ (C (b i))).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (C (b i))).continuous.tendsto _).comp
        hsecond)).sub
    (((ContinuousLinearMap.apply ℝ ℝ (C (b i))).continuous.tendsto _).comp
      (((fderiv ℝ B x (C (b i))).continuous.tendsto _).comp ha))
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hterm i)
  have hresult := ((tendsto_const_nhds (x := ρ x)).mul hsum).add
    (((fderiv ℝ ρ x).continuous.tendsto _).comp ha)
  have hseq (j : ℕ) := trace_weightedMetricDual_eq b hB hρ (hf j) hi C hC
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply] at hresult
  simpa only [← trace_weightedMetricDual_eq b hB hρ hu hi C hC, ← hseq] using hresult

end PoincareConjecture.M10
