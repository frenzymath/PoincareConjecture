import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.RegularizedOperator
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Actual bounded compact smooth approximants

The normalized positive radial bump kernels have fixed radius ratio
three. Their actual convolutions retain the bound and a common compact
support, and converge almost everywhere by Lebesgue differentiation.
Source: M65 derivation 32, bounded smooth approximation, for MT
Lemma 19.2, printed pp. 438--439; Eschenburg--Tribuzy,
Cauchy--Riemann inequalities, preprint pp. 8--11.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology Convolution ContDiff

namespace PoincareMT.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual normalized bump convolution constructs smooth approximants
with the original uniform bound and a common compact support. No
approximation premise is supplied. Source: derivation 32, bounded
smooth approximation, for MT 19.2, pp. 438--439. -/
theorem exists_smooth_bounded_approximation {h : ℂ → E} {R B : ℝ}
    (hB : 0 ≤ B) (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖h z‖ ≤ B) :
    ∃ f : ℕ → ℂ → E,
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) (R + 1)) ∧
      (∀ n z, ‖f n z‖ ≤ B) ∧
      ∀ᵐ z ∂volume, Tendsto (fun n => f n z) atTop (𝓝 (h z)) := by
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ 1 := by
    dsimp only [δ]
    exact div_le_one_of_le₀ (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      (by positivity)
  let φ (n : ℕ) : ContDiffBump (0 : ℂ) :=
    { rIn := δ n / 3
      rOut := δ n
      rIn_pos := div_pos (hδ n) (by norm_num)
      rIn_lt_rOut := by linarith [hδ n] }
  let f (n : ℕ) : ℂ → E :=
    (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h
  have hi : LocallyIntegrable h volume :=
    (integrable_of_bound_support hh hs hb).locallyIntegrable
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ n).contDiff_normed hi
  have hfs (n : ℕ) : Function.support (f n) ⊆ closedBall (0 : ℂ) (R + 1) := by
    intro z hz
    obtain ⟨a, ha, b, hb', hab⟩ :=
      support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hz
    have haδ : ‖a‖ ≤ δ n := by
      rw [(φ n).support_normed_eq] at ha
      exact (mem_ball_zero_iff.mp ha).le
    have hbR : ‖b‖ ≤ R := mem_closedBall_zero_iff.mp (hs hb')
    apply mem_closedBall_zero_iff.mpr
    rw [← hab]
    exact (norm_add_le a b).trans (by linarith [hδle n])
  have hfb (n : ℕ) (z : ℂ) : ‖f n z‖ ≤ B := by
    have hd := dist_convolution_le (μ := (volume : Measure ℂ))
      (g := h) (x₀ := z) (z₀ := (0 : E)) hB
      ((φ n).support_normed_eq.subset) (φ n).nonneg_normed (φ n).integral_normed hh
      (fun w _ => by simpa only [dist_zero_right] using hb w)
    simpa only [dist_zero_right] using hd
  refine ⟨f, hf, hfs, hfb, ?_⟩
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := φ) (K := 3) ?_ ?_ hi
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Eventually.of_forall fun n => by dsimp only [φ]; linarith

end PoincareMT.M65Branch
