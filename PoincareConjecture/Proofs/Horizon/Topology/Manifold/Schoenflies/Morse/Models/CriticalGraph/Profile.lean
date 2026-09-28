import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped ContDiff Topology

namespace Poincare.Manifold.Schoenflies



def minimumCapWeight (u : Real) : Real := Real.smoothTransition (4 * u - 1)


def minimumCapDenominator (u : Real) : Real :=
  (1 - minimumCapWeight u) + minimumCapWeight u * u


def minimumCapSquaredRadius (u : Real) : Real := u / minimumCapDenominator u

theorem minimumCapWeight_zero {u : Real} (hu : u ≤ 1 / 4) : minimumCapWeight u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem minimumCapWeight_one {u : Real} (hu : 1 / 2 ≤ u) : minimumCapWeight u = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem minimumCapDenominator_pos (u : Real) : 0 < minimumCapDenominator u := by
  by_cases hu : u ≤ 1 / 4
  · simp [minimumCapDenominator, minimumCapWeight_zero hu]
  have hw0 : 0 ≤ minimumCapWeight u := Real.smoothTransition.nonneg _
  have hw1 : minimumCapWeight u ≤ 1 := Real.smoothTransition.le_one _
  have hmul := mul_nonneg hw0 (show 0 ≤ u - 1 / 4 by linarith)
  dsimp only [minimumCapDenominator]
  nlinarith

theorem contDiff_minimumCapWeight : ContDiff Real ∞ minimumCapWeight :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem monotone_minimumCapWeight : Monotone minimumCapWeight :=
  fun x y hxy => Real.smoothTransition.monotone (by linarith)

theorem contDiff_minimumCapDenominator : ContDiff Real ∞ minimumCapDenominator :=
  (contDiff_const.sub contDiff_minimumCapWeight).add (contDiff_minimumCapWeight.mul contDiff_id)

theorem contDiff_minimumCapSquaredRadius : ContDiff Real ∞ minimumCapSquaredRadius :=
  contDiff_id.div contDiff_minimumCapDenominator (fun u => (minimumCapDenominator_pos u).ne')

theorem minimumCapSquaredRadius_eq_self {u : Real} (hu : u ≤ 1 / 4) :
    minimumCapSquaredRadius u = u := by
  simp [minimumCapSquaredRadius, minimumCapDenominator, minimumCapWeight_zero hu]

theorem minimumCapSquaredRadius_eq_one {u : Real} (hu : 1 / 2 ≤ u) :
    minimumCapSquaredRadius u = 1 := by
  have hu0 : u ≠ 0 := by linarith
  simp [minimumCapSquaredRadius, minimumCapDenominator, minimumCapWeight_one hu, hu0]

theorem deriv_minimumCapSquaredRadius (u : Real) :
    deriv minimumCapSquaredRadius u =
      (1 - minimumCapWeight u + u * (1 - u) * deriv minimumCapWeight u) /
        minimumCapDenominator u ^ 2 := by
  have hw := (contDiff_minimumCapWeight.differentiable (by simp) u).hasDerivAt
  have hD : HasDerivAt minimumCapDenominator
      (-deriv minimumCapWeight u + (deriv minimumCapWeight u * u + minimumCapWeight u)) u := by
    convert! ((hasDerivAt_const u (1 : Real)).sub hw).add (hw.mul (hasDerivAt_id u)) using 1
    simp
  have hd := (hasDerivAt_id u).div hD (minimumCapDenominator_pos u).ne'
  change HasDerivAt minimumCapSquaredRadius _ u at hd
  rw [hd.deriv]
  simp only [id_eq]
  unfold minimumCapDenominator
  congr 1
  ring



theorem deriv_minimumCapSquaredRadius_pos {u : Real} (hu : u < 1 / 2) :
    0 < deriv minimumCapSquaredRadius u := by
  by_cases hu0 : u < 0
  · have heq : minimumCapSquaredRadius =ᶠ[𝓝 u] id := by
      filter_upwards [gt_mem_nhds (show u < 1 / 4 by linarith)] with x hx
      exact minimumCapSquaredRadius_eq_self hx.le
    rw [heq.deriv_eq, deriv_id]
    exact zero_lt_one
  have hwd : 0 ≤ deriv minimumCapWeight u := monotone_minimumCapWeight.deriv_nonneg
  have hw1 : minimumCapWeight u < 1 :=
    Real.smoothTransition.lt_one_of_lt_one (by linarith)
  have hprod := mul_nonneg (mul_nonneg (le_of_not_gt hu0)
    (show 0 ≤ 1 - u by linarith)) hwd
  rw [deriv_minimumCapSquaredRadius]
  exact div_pos (by linarith) (sq_pos_of_pos (minimumCapDenominator_pos u))

theorem strictMonoOn_minimumCapSquaredRadius :
    StrictMonoOn minimumCapSquaredRadius (Icc (0 : Real) (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    contDiff_minimumCapSquaredRadius.continuous.continuousOn
  intro u hu
  rw [interior_Icc] at hu
  exact deriv_minimumCapSquaredRadius_pos hu.2



theorem exists_unique_minimumCap_height {z : Real} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃! u : Real, u ∈ Ico (0 : Real) (1 / 2) ∧ minimumCapSquaredRadius u = z := by
  have h0 : minimumCapSquaredRadius 0 = 0 := minimumCapSquaredRadius_eq_self (by norm_num)
  have h1 : minimumCapSquaredRadius (1 / 2) = 1 := minimumCapSquaredRadius_eq_one le_rfl
  have hzimage : z ∈ minimumCapSquaredRadius '' Icc (0 : Real) (1 / 2) := by
    apply intermediate_value_Icc (by norm_num : (0 : Real) ≤ 1 / 2)
      contDiff_minimumCapSquaredRadius.continuous.continuousOn
    simpa only [h0, h1] using (show z ∈ Icc (0 : Real) 1 from ⟨hz, hz1.le⟩)
  obtain ⟨u, hu, huz⟩ := hzimage
  have hu1 : u < 1 / 2 := by
    apply lt_of_le_of_ne hu.2
    intro heq
    rw [heq, h1] at huz
    linarith
  refine ⟨u, ⟨⟨hu.1, hu1⟩, huz⟩, ?_⟩
  rintro w ⟨hw, hwz⟩
  exact strictMonoOn_minimumCapSquaredRadius.injOn
    ⟨hw.1, hw.2.le⟩ hu (hwz.trans huz.symm)

end Poincare.Manifold.Schoenflies
