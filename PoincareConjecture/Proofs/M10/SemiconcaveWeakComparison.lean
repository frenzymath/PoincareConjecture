import PoincareConjecture.Proofs.M10.SemiconcaveSmoothing
import PoincareConjecture.Proofs.M10.WeightedOperatorBound
import PoincareConjecture.Proofs.M10.WeightedOperatorLimit
import PoincareConjecture.Proofs.M10.WeightedTestIntegrable
import PoincareConjecture.Proofs.M10.UniformIntegralLimit
import PoincareConjecture.Proofs.M10.UpperIntegralLimit

set_option autoImplicit false

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

noncomputable local instance weakComparisonBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance weakComparisonBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem integral_weighted_comparison_of_semiconcave {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ u H ψ : E → ℝ}
    {x₀ : E} {r K S : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hu : ContinuousOn u (ball x₀ (4 * r)))
    (hconc : ConcaveOn ℝ (ball x₀ (4 * r)) (fun x ↦ u x - euclideanQuadratic K x))
    (hB : ContDiffOn ℝ 1 B (ball x₀ r)) (hρ : ContDiffOn ℝ 1 ρ (ball x₀ r))
    (hi : ∀ x ∈ ball x₀ r, (B x).IsInvertible)
    (hsym : ∀ x ∈ ball x₀ r, ∀ v w, B x v w = B x w v)
    (hframe : ∀ x ∈ ball x₀ r, ∃ C : E ≃L[ℝ] E, ∀ v w, B x (C v) (C w) = inner ℝ v w)
    (hcoeff : ∀ x ∈ ball x₀ r, ‖fderiv ℝ B x‖ ≤ S ∧ ‖(B x).inverse‖ ≤ S ∧
      0 ≤ ρ x ∧ ρ x ≤ S ∧ ‖fderiv ℝ ρ x‖ ≤ S)
    (hregular : ∀ᵐ x ∂μ, x ∈ ball x₀ r → ContDiffAt ℝ 2 u x ∧
      LinearMap.trace ℝ E (fderiv ℝ (weightedMetricDual B ρ u) x).toLinearMap ≤ H x)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ ball x₀ r)
    (hpos : ∀ x, 0 ≤ ψ x) (hH : Integrable (fun x ↦ ψ x * H x) μ) :
    Integrable (fun x ↦ u x * LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ ψ) x).toLinearMap) μ ∧
    (∫ x, u x * LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ ψ) x).toLinearMap ∂μ) ≤ ∫ x, ψ x * H x ∂μ := by
  obtain ⟨f, ε, G, hG, hε, _, hf, herr, hgrad, hhess, hjets⟩ :=
    exists_semiconcave_smoothing (μ := μ) hr hK hu hconc
  have hf2 (j : ℕ) : ContDiff ℝ 2 (f j) := (hf j).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
  have hsmall : ball x₀ r ⊆ ball x₀ (4 * r) := ball_subset_ball (by linarith)
  have htest := integrable_mul_trace_weighted_test (μ := μ) b isOpen_ball hB hρ hi
    (hu.mono hsmall) hψ hc hs
  have hgreen (j : ℕ) := integral_weighted_green (μ := μ) b isOpen_ball hB hρ hi hsym
    (hf2 j).contDiffOn hψ hc hs
  let v := fun x ↦ LinearMap.trace ℝ E (fderiv ℝ (weightedMetricDual B ρ ψ) x).toLinearMap
  let a := fun j x ↦ ψ x * LinearMap.trace ℝ E
    (fderiv ℝ (weightedMetricDual B ρ (f j)) x).toLinearMap
  let C := S * (Fintype.card ι : ℝ) * (K + S * S * G) * S + S * S * G
  have hsup : tsupport v ⊆ tsupport ψ :=
    (tsupport_trace_fderiv_subset _).trans (tsupport_weightedMetricDual_subset B ρ ψ)
  have hint : Tendsto (fun j ↦ ∫ x, a j x ∂μ) atTop (𝓝 (∫ x, u x * v x ∂μ)) := by
    have ht := tendsto_integral_mul_of_uniform_error htest.1 htest.2
      (fun j ↦ (hgreen j).1) hε
      (fun j x hx ↦ herr j x (hs (hsup (subset_tsupport v hx))))
    simpa only [(hgreen _).2.2] using ht
  refine ⟨htest.2, integral_limit_le_of_ae_upper_bound
    (fun j ↦ (hgreen j).2.1) hH
    ((hψ.continuous.integrable_of_hasCompactSupport hc).mul_const C) ?_ ?_ hint⟩
  · intro j
    exact Eventually.of_forall (fun x ↦ by
      by_cases hx : x ∈ tsupport ψ
      · have hxU := hs hx
        obtain ⟨A, hA⟩ := hframe x hxU
        obtain ⟨hDB, hI, hρ0, hρS, hdρ⟩ := hcoeff x hxU
        have hbound := trace_weightedMetricDual_le b
          (hB.contDiffAt (isOpen_ball.mem_nhds hxU))
          ((hρ.contDiffAt (isOpen_ball.mem_nhds hxU)).differentiableAt one_ne_zero)
          (hf2 j).contDiffAt (hi x hxU) A hA hK hS hS hG hS hS
          hDB hI (hgrad j x hxU) hρ0 hρS hdρ (hhess j x hxU)
        exact mul_le_mul_of_nonneg_left hbound (hpos x)
      · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, le_refl])
  · filter_upwards [hregular] with x hx
    by_cases hxs : x ∈ tsupport ψ
    · have hxU := hs hxs
      obtain ⟨hux, huxH⟩ := hx hxU
      obtain ⟨A, hA⟩ := hframe x hxU
      have hlim := trace_weightedMetricDual_tendsto b
        (hB.contDiffAt (isOpen_ball.mem_nhds hxU))
        ((hρ.contDiffAt (isOpen_ball.mem_nhds hxU)).differentiableAt one_ne_zero)
        hux (fun j ↦ (hf2 j).contDiffAt) (hi x hxU) A hA
        (hjets x hxU hux).1 (hjets x hxU hux).2
      exact ⟨_, tendsto_const_nhds.mul hlim,
        mul_le_mul_of_nonneg_left huxH (hpos x)⟩
    · refine ⟨0, ?_, ?_⟩ <;>
        simp only [image_eq_zero_of_notMem_tsupport hxs, zero_mul, le_refl,
          tendsto_const_nhds]

end PoincareConjecture.M10
