import PoincareConjecture.Definitions.Ch16.ControlledSurgery

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

theorem inverse_scalar_duration_bounds {r Q : ℝ}
    (hr : 0 < r) (hscalar : r⁻¹ ^ 2 ≤ Q) :
    0 < Q ∧ 0 < Q⁻¹ ∧ Q⁻¹ ≤ r ^ 2 := by
  have hthreshold : 0 < r⁻¹ ^ 2 := pow_pos (inv_pos.mpr hr) 2
  have hQ : 0 < Q := hthreshold.trans_le hscalar
  refine ⟨hQ, inv_pos.mpr hQ, ?_⟩
  have hi := (inv_le_inv₀ hQ hthreshold).mpr hscalar
  simpa only [← inv_pow, inv_inv] using hi

theorem firstFailure_neck_bottom_after_overlap
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {t r Q : ℝ} (hr : 0 < r) (hrLast : r ≤ p.r (Fin.last p.i))
    (ht : surgeryEpochStart p.i ≤ t) (hscalar : r⁻¹ ^ 2 ≤ Q) :
    surgeryEpochStart (p.i - 1) < t - Q⁻¹ := by
  have hduration := (inverse_scalar_duration_bounds hr hscalar).2.2
  have hrsmall : r ≤ 1 / 200 :=
    hrLast.trans ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _)))
  have hrsq : r ^ 2 < (1 / 32 : ℝ) := by
    have hsq := pow_le_pow_left₀ hr.le hrsmall 2
    norm_num at hsq
    linarith
  have hprevious : 1 / 32 ≤ surgeryEpochStart (p.i - 1) :=
    div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (by norm_num)
  have hepoch : surgeryEpochStart p.i = 2 * surgeryEpochStart (p.i - 1) := by
    calc
      surgeryEpochStart p.i = surgeryEpochStart (p.i - 1 + 1) := by
        rw [Nat.sub_add_cancel p.i_pos]
      _ = 2 * surgeryEpochStart (p.i - 1) := by
        unfold surgeryEpochStart
        rw [pow_succ]
        ring
  rw [hepoch] at ht
  linarith

theorem firstFailure_neck_window_subset_overlap
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {t r Q : ℝ}
    (hr : 0 < r) (hrLast : r ≤ p.r (Fin.last p.i))
    (ht : t ∈ Ico (surgeryEpochStart p.i) O.H) (hscalar : r⁻¹ ^ 2 ≤ Q) :
    Icc (t - Q⁻¹) t ⊆ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H := by
  have hbottom := firstFailure_neck_bottom_after_overlap p hr hrLast ht.1 hscalar
  have hprevious : 0 ≤ surgeryEpochStart (p.i - 1) := by
    unfold surgeryEpochStart
    positivity
  intro s hs
  have hlower := hbottom.trans_le hs.1
  have hupper := hs.2.trans_lt ht.2
  exact ⟨⟨hprevious.trans hlower.le, hupper⟩, hlower.le, hupper⟩

theorem firstFailure_neck_window_delta
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {t r Q delta : ℝ}
    (hr : 0 < r) (hrLast : r ≤ p.r (Fin.last p.i))
    (ht : t ∈ Ico (surgeryEpochStart p.i) O.H) (hscalar : r⁻¹ ^ 2 ≤ Q)
    (overlap : ∀ s ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta s ≤ delta) :
    ∀ s ∈ Icc (t - Q⁻¹) t, F.parameters.delta s ≤ delta := by
  intro s hs
  exact overlap s (firstFailure_neck_window_subset_overlap p hr hrLast ht hscalar hs)

end PoincareConjecture.Proofs.M47
