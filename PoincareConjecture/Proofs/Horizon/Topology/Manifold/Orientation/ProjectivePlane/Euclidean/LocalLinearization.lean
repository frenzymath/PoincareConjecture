import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology unitInterval

universe u v

namespace Poincare.Topology.Orientation.ProjectivePlane

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem exists_ball_linearization_bound {f : E → F} {x : E}
    (L : E ≃L[Real] F) (hf : HasFDerivAt f L.toContinuousLinearMap x) :
    ∃ r : Real, 0 < r ∧ ∀ y ∈ ball x r, y ≠ x →
      ‖f y - f x - L (y - x)‖ < ‖L (y - x)‖ := by
  let c : Real := ‖L.symm.toContinuousLinearMap‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have heps : 0 < (2 * c)⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp (hf.isLittleO.bound heps)
  refine ⟨r, hr, ?_⟩
  intro y hy hxy
  have hb := hbound (mem_ball.mp hy)
  have hL : 0 < ‖L (y - x)‖ := norm_pos_iff.mpr (by
    intro h
    exact hxy (sub_eq_zero.mp (L.injective (h.trans L.map_zero.symm))))
  have hi : ‖y - x‖ ≤ c * ‖L (y - x)‖ := by
    calc
      ‖y - x‖ = ‖L.symm (L (y - x))‖ := by rw [L.symm_apply_apply]
      _ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L (y - x)‖ :=
        L.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ c * ‖L (y - x)‖ := by dsimp [c]; nlinarith [norm_nonneg (L (y - x))]
  have he : (2 * c)⁻¹ * c = (1 / 2 : Real) := by field_simp
  calc
    ‖f y - f x - L (y - x)‖ ≤ (2 * c)⁻¹ * ‖y - x‖ := hb
    _ ≤ (2 * c)⁻¹ * (c * ‖L (y - x)‖) := mul_le_mul_of_nonneg_left hi heps.le
    _ = (1 / 2 : Real) * ‖L (y - x)‖ := by rw [← mul_assoc, he]
    _ < ‖L (y - x)‖ := by linarith

theorem exists_ball_linearization_homotopy {f : E → F} {x : E} {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U) (hcont : ContinuousOn f U)
    (L : E ≃L[Real] F) (hf : HasFDerivAt f L.toContinuousLinearMap x) :
    ∃ (r : Real) (_ : 0 < r) (hrU : ball x r ⊆ U),
      ∃ H : ContinuousMap.Homotopy
        (⟨fun y : ball x r => f x + L (y.val - x), by fun_prop⟩ : C(ball x r, F))
        (⟨fun y : ball x r => f y.val,
          (hcont.mono hrU).domRestrict⟩ : C(ball x r, F)),
        ∀ (t : unitInterval) (y : ball x r), y.val ≠ x → H (t, y) ≠ f x := by
  obtain ⟨s, hs, hb⟩ := exists_ball_linearization_bound L hf
  obtain ⟨q, hq, hqU⟩ := Metric.isOpen_iff.mp hU x hx
  let r := min s q
  have hr : 0 < r := lt_min hs hq
  have hrU : ball x r ⊆ U := (ball_subset_ball (min_le_right s q)).trans hqU
  have hfc : Continuous (fun y : ball x r => f y.val) :=
    (hcont.mono hrU).domRestrict
  let H : ContinuousMap.Homotopy
      (⟨fun y : ball x r => f x + L (y.val - x), by fun_prop⟩ : C(ball x r, F))
      (⟨fun y : ball x r => f y.val, hfc⟩ : C(ball x r, F)) :=
    { toFun := fun z => f x + L (z.2.val - x) +
        (z.1 : Real) • (f z.2.val - f x - L (z.2.val - x))
      continuous_toFun := by
        have hlin : Continuous (fun z : unitInterval × ball x r => L (z.2.val - x)) :=
          L.continuous.comp ((continuous_subtype_val.comp continuous_snd).sub continuous_const)
        exact (continuous_const.add hlin).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (((hfc.comp continuous_snd).sub continuous_const).sub hlin))
      map_zero_left := by intro y; simp
      map_one_left := by intro y; simp }
  refine ⟨r, hr, hrU, H, ?_⟩
  intro t y hxy he
  have hb' := hb y.val (ball_subset_ball (min_le_left s q) y.property) hxy
  have hv : L (y.val - x) = -((t : Real) • (f y.val - f x - L (y.val - x))) := by
    change f x + L (y.val - x) +
      (t : Real) • (f y.val - f x - L (y.val - x)) = f x at he
    apply eq_neg_iff_add_eq_zero.mpr
    exact add_left_cancel (show f x + (L (y.val - x) +
      (t : Real) • (f y.val - f x - L (y.val - x))) = f x + 0 by
      simpa only [add_assoc, add_zero] using he)
  have hn : ‖L (y.val - x)‖ ≤ ‖f y.val - f x - L (y.val - x)‖ := by
    calc
      ‖L (y.val - x)‖ = |(t : Real)| * ‖f y.val - f x - L (y.val - x)‖ := by
        calc
          _ = ‖-((t : Real) • (f y.val - f x - L (y.val - x)))‖ := congrArg norm hv
          _ = _ := by rw [norm_neg, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖f y.val - f x - L (y.val - x)‖ :=
        mul_le_mul_of_nonneg_right (by simpa [abs_of_nonneg t.property.1] using t.property.2)
          (norm_nonneg _)
      _ = _ := one_mul _
  exact (not_lt_of_ge hn) hb'

end Poincare.Topology.Orientation.ProjectivePlane
