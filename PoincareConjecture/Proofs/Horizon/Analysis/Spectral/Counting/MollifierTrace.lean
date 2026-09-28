import PoincareConjecture.Proofs.Horizon.Analysis.Spectral.Counting.KernelTrace
import PoincareConjecture.Proofs.Horizon.Analysis.Spectral.Counting.Mollification








noncomputable section

open MeasureTheory Metric
open scoped ENNReal Convolution

namespace Poincare.Analysis.Spectral.Counting

open Poincare.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem mollifierKernel_memLp {ε : ℝ} (hε : 0 < ε) (x : E) :
    MemLp (fun y : E => mollifierEps hε (x - y)) 2 volume := by
  exact ((mollifierEps_continuous hε).memLp_of_hasCompactSupport
    (mollifierEps_compactSupport hε)).comp_measurePreserving
      (Measure.measurePreserving_sub_left volume x)


def mollifierKernel {ε : ℝ} (hε : 0 < ε) (x : E) : Lp ℝ 2 (volume : Measure E) :=
  (mollifierKernel_memLp hε x).toLp _

theorem inner_mollifierKernel_eq_convolution {ε : ℝ} (hε : 0 < ε)
    (u : Lp ℝ 2 (volume : Measure E)) (x : E) :
    inner ℝ (mollifierKernel hε x) u =
      (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (u : E → ℝ)) x := by
  rw [L2.inner_def, convolution_lsmul_swap]
  apply integral_congr_ae
  filter_upwards [(mollifierKernel_memLp hε x).coeFn_toLp] with y hy
  simp [mollifierKernel, hy, mul_comm]

theorem aestronglyMeasurable_inner_mollifierKernel {ε : ℝ} (hε : 0 < ε)
    (u : Lp ℝ 2 (volume : Measure E)) :
    AEStronglyMeasurable (fun x => inner ℝ (mollifierKernel hε x) u) volume := by
  simp_rw [inner_mollifierKernel_eq_convolution]
  exact ((mollifierEps_compactSupport hε).continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (mollifierEps_continuous hε)
      ((Lp.memLp u).locallyIntegrable (by norm_num))).aestronglyMeasurable

theorem norm_mollifierKernel_sq_le {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖mollifierKernel hε x‖ ^ 2 ≤
      ((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) / ε ^ d := by
  rw [mollifierKernel, norm_toLp_sq_eq_integral]
  exact integral_mollifierEps_sub_sq_le hε x

theorem norm_mollifierKernel_le {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖mollifierKernel hε x‖ ≤
      Real.sqrt (((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) /
        ε ^ d) := by
  apply (Real.le_sqrt (norm_nonneg _)
    (div_nonneg (le_of_lt mollifierEps_sq_bound_constant_pos) (by positivity))).mpr
  exact norm_mollifierKernel_sq_le hε x


def mollifyOn (S : Set E) (hS : MeasurableSet S) (hvol : volume S ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    Lp ℝ 2 (volume : Measure E) →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  kernelOn S hS hvol (mollifierKernel hε)
    (aestronglyMeasurable_inner_mollifierKernel hε)
    (Real.sqrt (((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) / ε ^ d))
    (Real.sqrt_nonneg _) (norm_mollifierKernel_le hε)

theorem mollifyOn_coeFn (S : Set E) (hS : MeasurableSet S) (hvol : volume S ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) (u : Lp ℝ 2 (volume : Measure E)) :
    ⇑(mollifyOn S hS hvol hε u) =ᵐ[volume]
      S.indicator (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (u : E → ℝ)) := by
  have h := kernelOn_coeFn S hS hvol (mollifierKernel hε)
    (aestronglyMeasurable_inner_mollifierKernel hε)
    (Real.sqrt (((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) / ε ^ d))
    (Real.sqrt_nonneg _) (norm_mollifierKernel_le hε) u
  simpa only [mollifyOn, inner_mollifierKernel_eq_convolution] using h

theorem mollifyOn_toLp_coeFn (S : Set E) (hS : MeasurableSet S) (hvol : volume S ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ} (hu : MemLp u 2 volume) :
    ⇑(mollifyOn S hS hvol hε (hu.toLp u)) =ᵐ[volume]
      S.indicator (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
  have h := mollifyOn_coeFn S hS hvol hε (hu.toLp u)
  rwa [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
    Filter.EventuallyEq.rfl hu.coeFn_toLp] at h



theorem sum_norm_mollifyOn_map_sq_le
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Set E) (hS : MeasurableSet S) (hvol : volume S ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) (A : H →L[ℝ] Lp ℝ 2 (volume : Measure E))
    {b : ι → H} (hb : Orthonormal ℝ b) (s : Finset ι) :
    ∑ i ∈ s, ‖mollifyOn S hS hvol hε (A (b i))‖ ^ 2 ≤
      (volume : Measure E).real S * (‖A‖ ^ 2 *
        (((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) / ε ^ d)) := by
  exact sum_norm_kernelOn_map_sq_le S hS hvol (mollifierKernel hε)
    (aestronglyMeasurable_inner_mollifierKernel hε)
    (Real.sqrt (((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) / ε ^ d))
    (Real.sqrt_nonneg _) (norm_mollifierKernel_le hε) A hb s
    (norm_mollifierKernel_sq_le hε)

end Poincare.Analysis.Spectral.Counting
