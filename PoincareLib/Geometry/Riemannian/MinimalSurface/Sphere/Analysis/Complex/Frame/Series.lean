import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Complex.Frame.Estimates
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Complex.CauchyRiemann.Polar
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Convergence and invertibility of the holomorphic-frame series

Sacks-Uhlenbeck Theorem 1.6, p. 5, uses a local invertible frame for the
Cauchy-Riemann system. Geometric bounds on the actual Neumann terms and
their derivatives give a C1 sum within distance one of the identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT.M60

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [CompleteSpace V]

/-- The actual sum of the Cauchy-transform Neumann terms. Summability is
proved under the small-coefficient hypotheses below. Source:
SU Theorem 1.6, p. 5, local holomorphic-frame derivation. -/
noncomputable def holomorphicFrameSum (A : ℂ → V →L[ℂ] V) (z : ℂ) : V →L[ℂ] V :=
  ∑' j, holomorphicFrameTerm A j z

/-- Both the Neumann terms and their first derivatives are summable.
Source: SU Theorem 1.6, p. 5, local holomorphic-frame derivation. -/
theorem summable_holomorphicFrameTerm {A : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hq1 : q < 1)
    (hsmall : 2 * cauchyKernelNorm * a ≤ q)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) (z : ℂ) :
    Summable (fun j => holomorphicFrameTerm A j z) ∧
      Summable (fun j => fderiv ℝ (holomorphicFrameTerm A j) z) := by
  have hb := holomorphicFrameTerm_bounds hA hc ha hq hsmall hAb hDAb
  have hgeo : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_lt_one hq hq1
  constructor
  · exact Summable.of_norm_bounded (f := fun j => holomorphicFrameTerm A j z)
      hgeo (fun j => (hb j z).1)
  · apply Summable.of_norm_bounded
      (f := fun j => fderiv ℝ (holomorphicFrameTerm A j) z) hgeo
    intro j
    exact (hb j z).2

/-- Termwise differentiation of the convergent actual frame series.
Source: SU Theorem 1.6, p. 5, local holomorphic-frame derivation. -/
theorem hasFDerivAt_holomorphicFrameSum {A : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hq1 : q < 1)
    (hsmall : 2 * cauchyKernelNorm * a ≤ q)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) (z : ℂ) :
    HasFDerivAt (holomorphicFrameSum A)
      (∑' j, fderiv ℝ (holomorphicFrameTerm A j) z) z := by
  have hb := holomorphicFrameTerm_bounds hA hc ha hq hsmall hAb hDAb
  exact hasFDerivAt_tsum (summable_geometric_of_lt_one hq hq1)
    (fun j w => ((contDiff_holomorphicFrameTerm hA hc j).differentiable (by simp) w).hasFDerivAt)
    (fun j w => (hb j w).2)
    (summable_holomorphicFrameTerm hA hc ha hq hq1 hsmall hAb hDAb 0).1 z

/-- The frame series is genuinely C1, including continuity of its derivative.
Source: SU Theorem 1.6, p. 5, local holomorphic-frame derivation. -/
theorem contDiff_holomorphicFrameSum {A : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hq1 : q < 1)
    (hsmall : 2 * cauchyKernelNorm * a ≤ q)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) :
    ContDiff ℝ 1 (holomorphicFrameSum A) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun z => ∑' j, fderiv ℝ (holomorphicFrameTerm A j) z, ?_,
    hasFDerivAt_holomorphicFrameSum hA hc ha hq hq1 hsmall hAb hDAb⟩
  apply continuous_tsum
    (fun j => (contDiff_holomorphicFrameTerm hA hc j).continuous_fderiv (by simp))
    (summable_geometric_of_lt_one hq hq1)
  exact fun j z => (holomorphicFrameTerm_bounds hA hc ha hq hsmall hAb hDAb j z).2

/-- The nonconstant tail of the frame sum is bounded by its geometric
majorant. Source: SU Theorem 1.6, p. 5, local holomorphic-frame derivation. -/
theorem norm_holomorphicFrameSum_sub_one_le {A : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hq1 : q < 1)
    (hsmall : 2 * cauchyKernelNorm * a ≤ q)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) (z : ℂ) :
    ‖holomorphicFrameSum A z - 1‖ ≤ (1 - q)⁻¹ - 1 := by
  have hs := (summable_holomorphicFrameTerm hA hc ha hq hq1 hsmall hAb hDAb z).1
  have heq : holomorphicFrameSum A z - 1 = ∑' j, holomorphicFrameTerm A (j + 1) z := by
    rw [holomorphicFrameSum, hs.tsum_eq_zero_add]
    simp only [holomorphicFrameTerm, add_sub_cancel_left]
  rw [heq]
  apply tsum_of_norm_bounded
  · convert! (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one hq hq1) using 1
    simp
  · intro j
    exact (holomorphicFrameTerm_bounds hA hc ha hq hsmall hAb hDAb (j + 1) z).1

/-- A sufficiently small coefficient gives an invertible frame at every
point. Source: SU Theorem 1.6, p. 5, local holomorphic-frame derivation. -/
theorem isUnit_holomorphicFrameSum {A : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    {a : ℝ} (ha : 0 ≤ a) (hsmall : 2 * cauchyKernelNorm * a ≤ 1 / 4)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) (z : ℂ) :
    IsUnit (holomorphicFrameSum A z) := by
  have hb := norm_holomorphicFrameSum_sub_one_le hA hc ha
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    hsmall hAb hDAb z
  have hlt : ‖1 - holomorphicFrameSum A z‖ < 1 := by
    rw [norm_sub_rev]
    norm_num at hb
    linarith
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hlt

end PoincareMT.M60
