




import Mathlib.Analysis.Calculus.BumpFunction.Convolution



open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

namespace Poincare.Analysis.Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]



theorem tendstoUniformly_normed_convolution
    (mu : Measure E) [mu.IsAddHaarMeasure] {f : E → ℝ} (hf : UniformContinuous f)
    {ρ : ℕ → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0)) :
    TendstoUniformly (fun n => (ρ n).normed mu ⋆[lsmul ℝ ℝ, mu] f) f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε)
  filter_upwards [hρ.eventually_lt_const hδ] with n hn
  intro x
  have hdist := dist_convolution_le (μ := mu) (f := (ρ n).normed mu)
    (g := f) (x₀ := x) (R := (ρ n).rOut) (z₀ := f x) (half_pos hε).le
    (ρ n).support_normed_eq.subset (ρ n).nonneg_normed (ρ n).integral_normed
    hf.continuous.aestronglyMeasurable
    (fun y hy => (hmod ((Metric.mem_ball.mp hy).trans hn)).le)
  rw [dist_comm]
  exact hdist.trans_lt (half_lt_self hε)

end Poincare.Analysis.Convolution
