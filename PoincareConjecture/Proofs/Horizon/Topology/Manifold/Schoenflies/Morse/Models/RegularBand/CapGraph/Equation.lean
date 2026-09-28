import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.IntermediateValue



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies



def boundedCapEquation (z t : Real) : Real :=
  z + Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2) * (t ^ 2 - z)

theorem contDiffAt_boundedCapEquation {z t : Real} (h : t ^ 2 + z ≠ 0) :
    ContDiffAt Real ∞ (fun u : Real × Real => boundedCapEquation u.1 u.2) (z, t) := by
  unfold boundedCapEquation
  have ht2 : ContDiffAt Real ∞ (fun u : Real × Real => u.2 ^ 2) (z, t) :=
    contDiffAt_snd.pow 2
  have hz : ContDiffAt Real ∞ (fun u : Real × Real => u.1) (z, t) := contDiffAt_fst
  have harg : ContDiffAt Real ∞
      (fun u : Real × Real => 4 * u.2 ^ 2 / (u.2 ^ 2 + u.1) - 2) (z, t) :=
    ((contDiffAt_const.mul ht2).div (ht2.add hz) h).sub contDiffAt_const
  exact contDiffAt_fst.add
    (((Real.smoothTransition.contDiff : ContDiff Real ∞ _).contDiffAt.comp (z, t) harg).mul
      ((contDiffAt_snd.pow 2).sub contDiffAt_fst))

theorem hasDerivAt_boundedCapEquation {z t : Real} (h : t ^ 2 + z ≠ 0) :
    HasDerivAt (boundedCapEquation z)
      (deriv Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2) *
        (8 * t * z / (t ^ 2 + z) ^ 2) * (t ^ 2 - z) +
        Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2) * (2 * t)) t := by
  unfold boundedCapEquation
  have harg : HasDerivAt (fun u : Real => 4 * u ^ 2 / (u ^ 2 + z) - 2)
      (8 * t * z / (t ^ 2 + z) ^ 2) t := by
    apply (((((hasDerivAt_id t).pow 2).const_mul 4).div
      (((hasDerivAt_id t).pow 2).add_const z) h).sub_const 2).congr_deriv
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    ring
  have htransition : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2))
      (4 * t ^ 2 / (t ^ 2 + z) - 2) :=
    ((Real.smoothTransition.contDiff : ContDiff Real ∞ _).differentiable
      (by simp)).differentiableAt.hasDerivAt
  simpa only [Nat.cast_ofNat, pow_one, mul_one, Pi.pow_apply, id_eq,
    Nat.reduceSub, Function.comp_apply, Pi.mul_apply] using
    ((htransition.comp t harg).mul (((hasDerivAt_id t).pow 2).sub_const z)).const_add z

theorem deriv_boundedCapEquation_pos {z t : Real}
    (hz : 0 ≤ z) (hz1 : z < 1) (ht : 1 ≤ t) :
    0 < deriv (boundedCapEquation z) t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hden : 0 < t ^ 2 + z := by positivity
  rw [(hasDerivAt_boundedCapEquation hden.ne').deriv]
  have harg : 0 < 4 * t ^ 2 / (t ^ 2 + z) - 2 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  have hw := Real.smoothTransition.pos_of_pos harg
  have hd := Real.smoothTransition.monotone.deriv_nonneg
    (x := 4 * t ^ 2 / (t ^ 2 + z) - 2)
  have hnonneg : 0 ≤ deriv Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2) *
      (8 * t * z / (t ^ 2 + z) ^ 2) * (t ^ 2 - z) := by
    apply mul_nonneg
    · exact mul_nonneg hd (by positivity)
    · linarith
  exact add_pos_of_nonneg_of_pos hnonneg (mul_pos hw (by positivity))

theorem strictMonoOn_boundedCapEquation {z : Real} (hz : 0 ≤ z) (hz1 : z < 1) :
    StrictMonoOn (boundedCapEquation z) (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    exact (hasDerivAt_boundedCapEquation (show t ^ 2 + z ≠ 0 by
      have : 0 < t := by have := ht; change 1 ≤ t at this; linarith
      positivity)).continuousAt.continuousWithinAt
  · intro t ht
    exact deriv_boundedCapEquation_pos hz hz1 (interior_subset ht)

theorem one_le_of_boundedCapEquation_eq_one {z t : Real}
    (hz1 : z < 1) (ht : 0 ≤ t) (heq : boundedCapEquation z t = 1) : 1 ≤ t := by
  by_contra h
  have ht1 : t < 1 := lt_of_not_ge h
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hw0 := Real.smoothTransition.nonneg (4 * t ^ 2 / (t ^ 2 + z) - 2)
  have hw1 := Real.smoothTransition.le_one (4 * t ^ 2 / (t ^ 2 + z) - 2)
  have hstrict : (1 - Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2)) *
      (1 - z) + Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2) * (1 - t ^ 2) > 0 := by
    by_cases hw : Real.smoothTransition (4 * t ^ 2 / (t ^ 2 + z) - 2) = 0
    · rw [hw]; nlinarith
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr hw1) (by linarith))
        (mul_pos (lt_of_le_of_ne hw0 (Ne.symm hw)) (by linarith))
  unfold boundedCapEquation at heq
  nlinarith

theorem exists_unique_boundedCapEquation_height {z : Real} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃! t : Real, 0 ≤ t ∧ boundedCapEquation z t = 1 := by
  have hcont : ContinuousOn (boundedCapEquation z) (Icc 1 2) := by
    intro t ht
    exact (hasDerivAt_boundedCapEquation (show t ^ 2 + z ≠ 0 by
      have : 0 < t := by linarith [ht.1]
      positivity)).continuousAt.continuousWithinAt
  have hleft : boundedCapEquation z 1 ≤ 1 := by
    have hw := Real.smoothTransition.le_one (4 * 1 ^ 2 / (1 ^ 2 + z) - 2)
    have h := mul_le_mul_of_nonneg_right hw (show 0 ≤ 1 - z by linarith)
    simpa only [boundedCapEquation, one_pow] using (show z +
      Real.smoothTransition (4 * 1 ^ 2 / (1 ^ 2 + z) - 2) * (1 - z) ≤ 1 by linarith)
  have hright : boundedCapEquation z 2 = 4 := by
    have hw : Real.smoothTransition (4 * 2 ^ 2 / (2 ^ 2 + z) - 2) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      have hd : 0 < (2 : Real) ^ 2 + z := by positivity
      have : 3 ≤ (4 : Real) * 2 ^ 2 / (2 ^ 2 + z) :=
        (le_div_iff₀ hd).mpr (by nlinarith)
      linarith
    unfold boundedCapEquation
    rw [hw]
    ring
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hcont (show (1 : Real) ∈ Icc (boundedCapEquation z 1) (boundedCapEquation z 2) by
      rw [hright]; exact ⟨hleft, by norm_num⟩)
  refine ⟨t, ⟨by linarith [ht.1], hteq⟩, ?_⟩
  intro u hu
  exact (strictMonoOn_boundedCapEquation hz hz1).injOn
    (one_le_of_boundedCapEquation_eq_one hz1 hu.1 hu.2) ht.1 (hu.2.trans hteq.symm)

end Poincare.Manifold.Schoenflies
