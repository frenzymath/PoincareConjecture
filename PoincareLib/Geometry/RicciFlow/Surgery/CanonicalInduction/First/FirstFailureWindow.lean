import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic

/-!
# Lemma 17.2: the strong-neck bottom in the controlled overlap

Morgan--Tian pp. 397-398, with Definition 15.7's dyadic epochs, p. 361.
The actual scalar need only be at least the radius threshold. Its inverse
duration is strictly shorter than the gap to the previous epoch, including
when the first failure lies at the old endpoint itself.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Proofs.M47

/-- High scalar bounds the actual backward neck duration without replacing
the scalar by its threshold, Morgan--Tian Lemma 17.2, p. 397. -/
theorem inverse_scalar_duration_bounds {r Q : ℝ}
    (hr : 0 < r) (hscalar : r⁻¹ ^ 2 ≤ Q) :
    0 < Q ∧ 0 < Q⁻¹ ∧ Q⁻¹ ≤ r ^ 2 := by
  have hthreshold : 0 < r⁻¹ ^ 2 := pow_pos (inv_pos.mpr hr) 2
  have hQ : 0 < Q := hthreshold.trans_le hscalar
  refine ⟨hQ, inv_pos.mpr hQ, ?_⟩
  have hi := (inv_le_inv₀ hQ hthreshold).mpr hscalar
  simpa only [← inv_pow, inv_inv] using hi

/-- The neck bottom lies strictly after the previous epoch, including at
the included first-failure boundary, Morgan--Tian pp. 397-398. -/
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

/-- The full closed neck window is contained in the literal observed
overlap where the induction cutoff is available, MT pp. 397-398. -/
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

/-- Restrict the supplied overlap cutoff to the actual closed neck window,
including its possible exposed surgery bottom, MT pp. 397-398. -/
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

end PoincareMT.Proofs.M47
