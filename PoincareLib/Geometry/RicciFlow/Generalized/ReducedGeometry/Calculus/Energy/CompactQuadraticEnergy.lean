import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartCoercivity

/-!
# L2 control from a compact family of positive quadratic forms

The local coordinate energy argument in Morgan-Tian Lemma 6.8,
pp. 108-109. M08's compact coercivity theorem converts integrability
of the actual positive quadratic energy into a fixed-norm L2 bound.
-/

set_option autoImplicit false

open Set Filter
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An integrable positive quadratic energy on a compact interval gives
L2 control in the fixed norm, the coordinate estimate used in Lemma 6.8,
pp. 108-109. Endpoint values of the measurable velocity are unrestricted. -/
theorem memLp_two_of_integrable_positive_quadratic {a b : ℝ} (hab : a ≤ b)
    (B : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (hB : ContinuousOn B (Icc a b))
    (hpos : ∀ s ∈ Icc a b, ∀ v : E, v ≠ 0 → 0 < B s v v)
    (d : ℝ → E) (hd : AEStronglyMeasurable d (volume.restrict (Icc a b)))
    (henergy : IntervalIntegrable (fun s => B s (d s) (d s)) volume a b) :
    MemLp d 2 (volume.restrict (Icc a b)) := by
  obtain ⟨c, hc, hcoercive⟩ :=
    PoincareMT.M08.compact_positive_forms_coercive isCompact_Icc B hB hpos
  have hq := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp henergy
  have hd2 : Integrable (fun s => ‖d s‖ ^ 2) (volume.restrict (Icc a b)) := by
    apply (hq.const_mul c⁻¹).mono' (hd.norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    change |‖d s‖ ^ 2| ≤ c⁻¹ * B s (d s) (d s)
    rw [abs_of_nonneg (sq_nonneg ‖d s‖)]
    calc
      ‖d s‖ ^ 2 = c⁻¹ * (c * ‖d s‖ ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * B s (d s) (d s) :=
        mul_le_mul_of_nonneg_left (hcoercive s hs (d s)) (inv_pos.mpr hc).le
  exact (memLp_two_iff_integrable_sq_norm hd).mpr hd2

end MeasureTheory
