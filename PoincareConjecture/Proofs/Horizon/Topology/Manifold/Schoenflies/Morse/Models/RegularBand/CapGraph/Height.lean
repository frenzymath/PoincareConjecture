import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Equation
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies

def boundedCapHeight (z : Real) : Real :=
  if h : 0 ≤ z ∧ z < 1 then
    Classical.choose (exists_unique_boundedCapEquation_height h.1 h.2)
  else 1

theorem boundedCapHeight_spec {z : Real} (hz : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ boundedCapHeight z ∧ boundedCapEquation z (boundedCapHeight z) = 1 := by
  rw [boundedCapHeight, dif_pos ⟨hz, hz1⟩]
  exact (Classical.choose_spec (exists_unique_boundedCapEquation_height hz hz1)).1

theorem boundedCapHeight_eq_of_equation {z t : Real} (hz : 0 ≤ z) (hz1 : z < 1)
    (ht : 0 ≤ t) (heq : boundedCapEquation z t = 1) : boundedCapHeight z = t := by
  exact (exists_unique_boundedCapEquation_height hz hz1).unique
    (boundedCapHeight_spec hz hz1) ⟨ht, heq⟩

theorem one_le_boundedCapHeight {z : Real} (hz : 0 ≤ z) (hz1 : z < 1) :
    1 ≤ boundedCapHeight z :=
  one_le_of_boundedCapEquation_eq_one hz1
    (boundedCapHeight_spec hz hz1).1 (boundedCapHeight_spec hz hz1).2

theorem boundedCapHeight_eq_one {z : Real} (hz : z ≤ 1 / 3) : boundedCapHeight z = 1 := by
  by_cases hz0 : 0 ≤ z
  · apply boundedCapHeight_eq_of_equation hz0 (by linarith) zero_le_one
    have hw : Real.smoothTransition (4 * 1 ^ 2 / (1 ^ 2 + z) - 2) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      have hd : 0 < (1 : Real) ^ 2 + z := by positivity
      have : 3 ≤ (4 : Real) * 1 ^ 2 / (1 ^ 2 + z) :=
        (le_div_iff₀ hd).mpr (by nlinarith)
      linarith
    unfold boundedCapEquation
    rw [hw]
    ring
  · simp [boundedCapHeight, hz0]

theorem contDiffAt_boundedCapHeight {z : Real} (hz1 : z < 1) :
    ContDiffAt Real ∞ boundedCapHeight z := by
  by_cases hzsmall : z < 1 / 3
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hzsmall] with y hy
    exact boundedCapHeight_eq_one hy.le
  have hz : 0 < z := by linarith
  let t := boundedCapHeight z
  have ht : 1 ≤ t := one_le_boundedCapHeight hz.le hz1
  have hden : t ^ 2 + z ≠ 0 := by positivity
  let f : Real × Real → Real := fun u => boundedCapEquation u.1 u.2
  have hf : ContDiffAt Real ∞ f (z, t) := contDiffAt_boundedCapEquation hden
  have hpartial : fderiv Real f (z, t) ∘L ContinuousLinearMap.inr Real Real Real =
      fderiv Real (boundedCapEquation z) t := by
    have he : DifferentiableAt Real (fun u : Real => (z, u)) t :=
      (differentiableAt_const z).prodMk differentiableAt_id
    have hde : fderiv Real (fun u : Real => (z, u)) t =
        ContinuousLinearMap.inr Real Real Real := by
      have hd : HasFDerivAt (fun u : Real => (z, u))
          (ContinuousLinearMap.inr Real Real Real) t := by
        have hc : HasFDerivAt (fun _ : Real => z) (0 : Real →L[Real] Real) t :=
          hasFDerivAt_const z t
        have hi : HasFDerivAt (fun u : Real => u)
            (ContinuousLinearMap.id Real Real) t := hasFDerivAt_id t
        simpa only [id_eq, ContinuousLinearMap.inr] using
          hc.prodMk hi
      exact hd.fderiv
    rw [← hde, ← fderiv_comp t (hf.differentiableAt (by simp)) he]
    rfl
  have hinv : (fderiv Real f (z, t) ∘L ContinuousLinearMap.inr Real Real Real).IsInvertible := by
    rw [hpartial]
    have hd : deriv (boundedCapEquation z) t ≠ 0 :=
      (deriv_boundedCapEquation_pos hz.le hz1 ht).ne'
    have hbij : Bijective (fderiv Real (boundedCapEquation z) t) := by
      constructor
      · intro x y hxy
        simp only [fderiv_eq_deriv_mul] at hxy
        exact mul_left_cancel₀ hd hxy
      · intro y
        refine ⟨y / deriv (boundedCapEquation z) t, ?_⟩
        rw [fderiv_eq_deriv_mul]
        exact mul_div_cancel₀ y hd
    exact ⟨ContinuousLinearEquiv.ofBijective _
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), rfl⟩
  let ψ := hf.implicitFunction (by simp) hinv
  have hψ : ContDiffAt Real ∞ ψ z := hf.contDiffAt_implicitFunction (by simp) hinv
  have hψz : ψ z = t := hf.implicitFunction_apply_self (by simp) hinv
  have hψeq : ∀ᶠ y in 𝓝 z, boundedCapEquation y (ψ y) = 1 := by
    simpa only [f, t, (boundedCapHeight_spec hz.le hz1).2] using
      hf.eventually_apply_implicitFunction (by simp) hinv
  have hψpos : ∀ᶠ y in 𝓝 z, 0 < ψ y :=
    hψ.continuousAt.eventually (lt_mem_nhds (show 0 < ψ z by rw [hψz]; linarith))
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hψeq, hψpos, gt_mem_nhds hz1, lt_mem_nhds hz] with y he hy hy1 hy0
  exact boundedCapHeight_eq_of_equation hy0.le hy1 hy.le he

theorem contDiffOn_boundedCapHeight : ContDiffOn Real ∞ boundedCapHeight (Iio 1) :=
  fun _ hz => (contDiffAt_boundedCapHeight hz).contDiffWithinAt

end Poincare.Manifold.Schoenflies
