import PoincareConjecture.Proofs.M10.WeightedMetricDual
import PoincareConjecture.Proofs.M10.WeightedTrace

set_option autoImplicit false

open scoped ContDiff BigOperators

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem trace_weightedMetricDual_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ f : E → ℝ} {x : E}
    (hB : ContDiffAt ℝ 1 B x) (hρ : DifferentiableAt ℝ ρ x) (hf : ContDiffAt ℝ 2 f x)
    (hi : (B x).IsInvertible) (C : E ≃L[ℝ] E)
    (hC : ∀ v w, B x (C v) (C w) = inner ℝ v w) :
    LinearMap.trace ℝ E (fderiv ℝ (weightedMetricDual B ρ f) x).toLinearMap =
      ρ x * (∑ i, (fderiv ℝ (fderiv ℝ f) x (C (b i)) (C (b i)) -
        fderiv ℝ B x (C (b i)) ((B x).inverse (fderiv ℝ f x)) (C (b i)))) +
      fderiv ℝ ρ x ((B x).inverse (fderiv ℝ f x)) := by
  unfold weightedMetricDual
  rw [trace_fderiv_smul hρ
    ((metricDual_contDiffAt hB hf hi).differentiableAt one_ne_zero),
    trace_eq_sum_normalized_metric b (B x) C hC]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have h := metricDual_fderiv_identity hB hf hi (C (b i)) (C (b i))
  change _ + _ = _ at h
  exact eq_sub_of_add_eq h

end PoincareConjecture.M10
