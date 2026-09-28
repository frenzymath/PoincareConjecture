import PoincareConjecture.Proofs.M10.MollifierBasics
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false

open Set Filter Metric MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

theorem normed_convolution_eqOn_of_eqOn (κ : ContDiffBump (0 : E))
    {f g : E → ℝ} {x : E} {r : ℝ} (hκ : κ.rOut ≤ r / 2)
    (hfg : EqOn f g (ball x r)) :
    EqOn (κ.normed μ ⋆[lsmul ℝ ℝ, μ] f)
      (κ.normed μ ⋆[lsmul ℝ ℝ, μ] g) (ball x (r / 2)) := by
  intro y hy
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  by_cases hz : κ.normed μ z = 0
  · simp only [hz, lsmul_apply, zero_smul]
  · have hzn : ‖z‖ < κ.rOut := by
      have hmem : z ∈ Function.support (κ.normed μ) := hz
      simpa only [κ.support_normed_eq, mem_ball, dist_zero_right] using hmem
    have hmem : y - z ∈ ball x r := by
      rw [mem_ball_iff_norm] at hy ⊢
      calc
        ‖y - z - x‖ = ‖(y - x) - z‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖z‖ := norm_sub_le _ _
        _ < r / 2 + r / 2 := add_lt_add hy (hzn.trans_le hκ)
        _ = r := add_halves r
    change κ.normed μ z * f (y - z) = κ.normed μ z * g (y - z)
    rw [hfg hmem]

theorem eventually_normed_convolution_eventuallyEq {κ : ℕ → ContDiffBump (0 : E)}
    (hκ : Tendsto (fun j ↦ (κ j).rOut) atTop (𝓝 0))
    {f g : E → ℝ} {x : E} (hfg : f =ᶠ[𝓝 x] g) :
    ∀ᶠ j in atTop, (κ j).normed μ ⋆[lsmul ℝ ℝ, μ] f =ᶠ[𝓝 x]
      (κ j).normed μ ⋆[lsmul ℝ ℝ, μ] g := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hfg
  have he : ∀ᶠ j in atTop, (κ j).rOut < r / 2 :=
    hκ (eventually_lt_nhds (half_pos hr))
  filter_upwards [he] with j hj
  exact (normed_convolution_eqOn_of_eqOn (κ j) hj.le hball).eventuallyEq_of_mem
    (ball_mem_nhds x (half_pos hr))

end PoincareConjecture.M10
