import PoincareConjecture.Proofs.M34.Mathlib.CapPersistenceBallSupremum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric

namespace Metric

theorem exists_pos_sSup_image_ball_eq_inv_sq_of_approximate_radial_projection
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X] (x : X)
    (hproject : ∀ R r ε : ℝ, 0 ≤ r → r ≤ R → 0 < ε →
      closedBall x R ⊆ thickening (R - r + ε) (closedBall x r))
    {f : X → ℝ} (hf : Continuous f) (hfx : 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (Real.sqrt (f x))⁻¹ ∧
      sSup (f '' ball x r) = r⁻¹ ^ 2 := by
  let R := (Real.sqrt (f x))⁻¹
  have hR : 0 < R := inv_pos.mpr (Real.sqrt_pos.mpr hfx)
  let S := fun r : ℝ => sSup (f '' closedBall x r)
  have hc : ContinuousOn S (Ici 0) :=
    continuousOn_sSup_image_closedBall_of_approximate_radial_projection hproject hf
  have hproduct : ContinuousOn (fun r => r ^ 2 * S r) (Icc 0 R) :=
    (continuousOn_id.pow 2).mul (hc.mono (fun _ h => h.1))
  have hbase : f x ≤ S R := le_csSup
    ((isCompact_closedBall x R).bddAbove_image hf.continuousOn)
    (mem_image_of_mem f (mem_closedBall_self hR.le))
  have hscale : R ^ 2 * f x = 1 := by
    dsimp [R]
    rw [inv_pow, Real.sq_sqrt hfx.le, inv_mul_cancel₀ hfx.ne']
  have hupper : 1 ≤ R ^ 2 * S R := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hbase (sq_nonneg R)
  obtain ⟨r, hr, hlevel⟩ := intermediate_value_Icc hR.le hproduct
    (show (1 : ℝ) ∈ Icc (0 ^ 2 * S 0) (R ^ 2 * S R) from ⟨by simp, hupper⟩)
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr.1
    intro he
    subst r
    norm_num at hlevel
  refine ⟨r, hrpos, hr.2, ?_⟩
  rw [sSup_image_ball_eq_closedBall_of_approximate_radial_projection hproject hf hrpos]
  change S r = r⁻¹ ^ 2
  apply (mul_left_cancel₀ (pow_ne_zero 2 hrpos.ne'))
  calc
    r ^ 2 * S r = 1 := hlevel
    _ = r ^ 2 * r⁻¹ ^ 2 := by field_simp

end Metric
