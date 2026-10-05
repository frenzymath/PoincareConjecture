import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedVolume
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Jacobian.WeightedJacobian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Scalar weighted Jacobian calculus on positive intervals

The actual tangential derivative and metric Jacobian evolution give
the logarithmic factor in Morgan-Tian Proposition 6.81, equations
6.19-6.21, pp. 145-146. The scalar Laplacian bound makes it
nonpositive. The argument never divides by the Jacobian and also
covers dimension zero and a merely continuous terminal endpoint.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.M14

/-- The square-time weighted Jacobian derivative follows from the
generic M10 product rule at dimension twice n, Proposition 6.81,
equations 6.19-6.21, pp. 145-146. -/
theorem squareWeightedJacobian_hasDerivAt {n : ℕ} {a J : ℝ → ℝ}
    {K R L s : ℝ} (hs : 0 < s) (ha : HasDerivAt a (-K / s ^ 2) s)
    (hJ : HasDerivAt J (2 * s * J s * (R + L)) s) :
    HasDerivAt (fun r => Real.rpow r (-(n : ℝ)) * Real.exp (-a r) * J r)
      ((Real.rpow s (-(n : ℝ)) * Real.exp (-a s) * J s) *
        (2 * s * (R + L) + K / s ^ 2 - (n : ℝ) / s)) s := by
  have hJ' : HasDerivAt J (J s * (2 * s * R + 2 * s * L)) s := by
    convert hJ using 1
    ring
  have h := M10.weightedJacobian_hasDerivAt (n := 2 * n) hs ha hJ'
  have hdim : -( ((2 * n : ℕ) : ℝ)) / 2 = -(n : ℝ) := by
    push_cast
    ring
  rw [hdim] at h
  apply h.congr_deriv
  congr 1
  push_cast
  ring

/-- The actual regular Laplacian bound gives a nonpositive scalar
weighted-Jacobian derivative without assuming J is positive,
Proposition 6.81, pp. 145-146. -/
theorem squareWeightedJacobian_deriv_nonpos {n : ℕ} {a J : ℝ → ℝ}
    {K R L s : ℝ} (hs : 0 < s) (ha : HasDerivAt a (-K / s ^ 2) s)
    (hJ : HasDerivAt J (2 * s * J s * (R + L)) s) (hJnonneg : 0 ≤ J s)
    (hL : L ≤ (n : ℝ) / (2 * s ^ 2) - R - K / (2 * s ^ 3)) :
    deriv (fun r => Real.rpow r (-(n : ℝ)) * Real.exp (-a r) * J r) s ≤ 0 := by
  rw [(squareWeightedJacobian_hasDerivAt hs ha hJ).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _)).le hJnonneg
  · have heq : 2 * s * (R + L) + K / s ^ 2 - (n : ℝ) / s =
        2 * s * (L - ((n : ℝ) / (2 * s ^ 2) - R - K / (2 * s ^ 3))) := by
      field_simp [hs.ne']
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_pos zero_lt_two hs).le (sub_nonpos.mpr hL)

/-- Interior evolution and terminal continuity give monotonicity
on the whole positive prefix, including its terminal endpoint,
Proposition 6.81, pp. 145-146. -/
theorem squareWeightedJacobian_antitoneOn {n : ℕ} {a J K R L : ℝ → ℝ} {b : ℝ}
    (ha : ContinuousOn a (Ioc 0 b)) (hJ : ContinuousOn J (Ioc 0 b))
    (ha' : ∀ s ∈ Ioo 0 b, HasDerivAt a (-K s / s ^ 2) s)
    (hJ' : ∀ s ∈ Ioo 0 b, HasDerivAt J (2 * s * J s * (R s + L s)) s)
    (hJnonneg : ∀ s ∈ Ioo 0 b, 0 ≤ J s)
    (hL : ∀ s ∈ Ioo 0 b,
      L s ≤ (n : ℝ) / (2 * s ^ 2) - R s - K s / (2 * s ^ 3)) :
    AntitoneOn (fun s => Real.rpow s (-(n : ℝ)) * Real.exp (-a s) * J s) (Ioc 0 b) := by
  have hp : ContinuousOn (fun s : ℝ => Real.rpow s (-(n : ℝ))) (Ioc 0 b) :=
    fun s hs => (Real.hasDerivAt_rpow_const (p := -(n : ℝ))
      (Or.inl hs.1.ne')).continuousAt.continuousWithinAt
  have hexp := Real.continuous_exp.comp_continuousOn ha.neg
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 b) ((hp.mul hexp).mul hJ)
  · intro s hs
    rw [interior_Ioc] at hs
    exact (squareWeightedJacobian_hasDerivAt (n := n) hs.1
      (ha' s hs) (hJ' s hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact squareWeightedJacobian_deriv_nonpos hs.1 (ha' s hs) (hJ' s hs)
      (hJnonneg s hs) (hL s hs)

/-- A positive-prefix antitone density is bounded by its initial
one-sided limit, the Gaussian comparison in Proposition 6.81,
pp. 145-146. -/
theorem positivePrefix_le_initial_limit {f : ℝ → ℝ} {b c s : ℝ}
    (hanti : AntitoneOn f (Ioc 0 b)) (hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hs : s ∈ Ioc 0 b) : f s ≤ c := by
  apply ge_of_tendsto hlim
  filter_upwards [Ioc_mem_nhdsGT hs.1] with r hr
  exact hanti ⟨hr.1, hr.2.trans hs.2⟩ hs hr.2

end PoincareMT.M14
