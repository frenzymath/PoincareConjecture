import PoincareConjecture.Proofs.M47.FirstFailureWindow

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

theorem blowup_analytic_window_subset_overlap
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {base Q T s R d : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hT : 0 ≤ T) (hScale : 64 * (T + 1) ≤ Q) (hR : Q ≤ R) (hd : d ≤ 1)
    (hs : s ∈ Ico (base - T / Q) base) :
    Icc (s - d / R) s ⊆ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H := by
  have hQpos : 0 < Q := by linarith
  have hRpos : 0 < R := hQpos.trans_le hR
  have hdR : d / R ≤ 1 / Q := by
    calc
      d / R ≤ 1 / R := div_le_div_of_nonneg_right hd hRpos.le
      _ ≤ 1 / Q := by simpa only [one_div] using inv_anti₀ hQpos hR
  have hshort : T / Q + 1 / Q ≤ 1 / 64 := by
    rw [← add_div]
    exact (div_le_iff₀ hQpos).mpr (by linarith)
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
  have hBottom : surgeryEpochStart (p.i - 1) < s - d / R := by
    rw [hEpoch] at hBase
    linarith [hBase.1, hs.1]
  intro u hu
  have hLower := hBottom.trans_le hu.1
  have hUpper := hu.2.trans_lt (hs.2.trans hBase.2)
  exact ⟨⟨by linarith, hUpper⟩, hLower.le, hUpper⟩

end PoincareConjecture.M47
