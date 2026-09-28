import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlatCap
import Mathlib.Analysis.InnerProductSpace.Calculus










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_bounded_flatCap_profile :
    ∃ a : E → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 1 ≤ a x) ∧
      (∀ x, ‖x‖ ≤ 1 / 4 → a x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹) ∧
      (∀ x, 1 / 2 ≤ ‖x‖ → a x = 1) ∧
      ∀ x, ‖x‖ < 1 → a x ≤ (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹ := by
  let b : E → ℝ := fun x => (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹
  have hrad (x : E) (hx : ‖x‖ < 1) : 0 < 1 - ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg x]
  have hb1 (x : E) (hx : ‖x‖ < 1) : 1 ≤ b x := by
    exact (one_le_inv₀ (Real.sqrt_pos.mpr (hrad x hx))).mpr
      (Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ‖x‖]))
  have hb : ContDiffOn ℝ ∞ b (ball (0 : E) (1 / 2)) := by
    exact ((contDiffOn_const.sub (contDiff_norm_sq ℝ).contDiffOn).sqrt
      (fun x hx => (hrad x (lt_trans (mem_ball_zero_iff.mp hx) (by norm_num))).ne')).inv
        (fun x hx => (Real.sqrt_pos.mpr
          (hrad x (lt_trans (mem_ball_zero_iff.mp hx) (by norm_num)))).ne')
  obtain ⟨a, ha, ha1, hnear, hfar, hbound⟩ := exists_smooth_profile_between
    (isCompact_closedBall (0 : E) (1 / 4)) isOpen_ball
    (closedBall_subset_ball (by norm_num : (1 / 4 : ℝ) < 1 / 2)) b hb
    (fun x hx => hb1 x (lt_trans (mem_ball_zero_iff.mp hx) (by norm_num)))
  refine ⟨a, ha, ha1, ?_, ?_, ?_⟩
  · intro x hx
    have hxK : x ∈ closedBall (0 : E) (1 / 4) := mem_closedBall_zero_iff.mpr hx
    exact (eventually_nhdsSet_iff_forall.mp hnear x hxK).self_of_nhds
  · intro x hx
    apply hfar
    simpa only [mem_ball_zero_iff, not_lt] using hx
  · intro x hx
    by_cases hxU : x ∈ ball (0 : E) (1 / 2)
    · exact hbound x hxU
    · rw [hfar x hxU]
      exact hb1 x hx



theorem exists_flatCap_profile :
    ∃ a : E → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧
      (∀ x, ‖x‖ ≤ 1 / 4 → a x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹) ∧
      ∀ x, 1 / 2 ≤ ‖x‖ → a x = 1 := by
  obtain ⟨a, ha, ha1, hnear, hfar, _⟩ := exists_bounded_flatCap_profile (E := E)
  exact ⟨a, ha, fun x => lt_of_lt_of_le zero_lt_one (ha1 x), hnear, hfar⟩

end PoincareConjecture.M25.Topology3D
