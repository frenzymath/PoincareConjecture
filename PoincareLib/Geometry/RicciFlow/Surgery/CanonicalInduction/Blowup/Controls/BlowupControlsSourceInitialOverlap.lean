import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsWindow

/-!
# The actual recent old event lies in the controlled overlap

The included age bound permits the old event to equal the original
base. Only epoch arithmetic is used at that endpoint.
Morgan--Tian Lemma 17.7, pp. 405-406; blowup-source-old-long-search.md, I8D1.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M47

/-- Every actual event within one original inverse-scalar unit of the
base has the overlap cutoff, including the zero-age endpoint. -/
theorem source_initial_recent_time_mem_overlap
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {base Q T : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hH : O.H ≤ surgeryEpochStart (p.i + 1)) (hQ : 128 ≤ Q)
    (hage : Q * (base - T) ∈ Icc (0 : ℝ) 1) :
    T ∈ surgeryObservationInterval O ∩ overlapInterval p := by
  have hQpos : 0 < Q := by linarith only [hQ]
  have hPast : T ≤ base := by
    have h := nonneg_of_mul_nonneg_right hage.1 hQpos
    linarith only [h]
  have hAge : base - T ≤ 1 / Q := by
    apply (le_div_iff₀ hQpos).mpr
    nlinarith only [hage.2]
  have hShort : 1 / Q ≤ (1 / 128 : ℝ) :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) hQ
  have hPrevious : 1 / 32 ≤ surgeryEpochStart (p.i - 1) :=
    div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (by norm_num)
  have hEpoch : surgeryEpochStart p.i = 2 * surgeryEpochStart (p.i - 1) := by
    calc
      surgeryEpochStart p.i = surgeryEpochStart (p.i - 1 + 1) := by
        rw [Nat.sub_add_cancel p.i_pos]
      _ = 2 * surgeryEpochStart (p.i - 1) := by
        unfold surgeryEpochStart
        rw [pow_succ]
        ring
  have hStart := hBase.1
  rw [hEpoch] at hStart
  have hLower : surgeryEpochStart (p.i - 1) < T := by
    linarith only [hStart, hAge, hShort, hPrevious]
  have hUpper : T < O.H := hPast.trans_lt hBase.2
  exact ⟨⟨by linarith only [hLower, hPrevious], hUpper⟩,
    hLower.le, hUpper.trans_le hH⟩

end PoincareMT.M47
