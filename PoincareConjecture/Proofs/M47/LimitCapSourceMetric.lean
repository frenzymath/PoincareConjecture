import PoincareConjecture.Proofs.M47.BlowupControlsSourceMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem normalized_source_metric_exp_upper
    (P : M44CapPersistencePredecessors.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} (hpinch : SurgeryFlowPinched F)
    {base Q a K : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C base Q (Icc a 0) U) (hU : IsOpen U) (ha : a ≤ 0)
    (hRm : ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
      (F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs x) ≤ K * Q) :
    ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      e.pullbackInner s hs x v v ≤
        Real.exp (6 * K * (-s)) * e.pullbackInner 0 ⟨ha, le_rfl⟩ x v v := by
  classical
  have hQ := e.scale_pos
  have hmem : MapsTo (fun z : ℝ => Q * z) (Icc (a / Q) 0) (Icc a 0) := by
    intro z hz
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hQ).mp hz.1,
      mul_nonpos_of_nonneg_of_nonpos hQ.le hz.2⟩
  have hmono : StrictMonoOn (fun z : ℝ => Q * z) (Icc (a / Q) 0) :=
    fun _ _ _ _ h => mul_lt_mul_of_pos_left h hQ
  have hclock (z : ℝ) (_hz : z ∈ Icc (a / Q) 0) :
      base + z / 1 = base + (Q * z) / Q := by
    rw [div_one, mul_div_cancel_left₀ z hQ.ne']
  let f : SurgeryFlowCylinder F C base 1 (Icc (a / Q) 0) U :=
    Proofs.M47.seedCylinderReclock e (by norm_num) ordConnected_Icc
      (fun z => Q * z) hmem hmono hclock
  have hfRm (z : ℝ) (hz : z ∈ Icc (a / Q) 0) (x : C.carrier) (hx : x ∈ U) :
      (F.connection (base + z / 1)).curvatureTensorNorm (f.forward z hz x) ≤ K * Q :=
    Proofs.M47.seedCylinderReclock_curvature e (by norm_num) ordConnected_Icc
      (fun z => Q * z) hmem hmono hclock hRm z hz x hx
  intro s hs x hx v
  have hsQ : s / Q ∈ Icc (a / Q) 0 :=
    ⟨div_le_div_of_nonneg_right hs.1 hQ.le, div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le⟩
  have hzero : (0 : ℝ) ∈ Icc (a / Q) 0 :=
    ⟨div_nonpos_of_nonpos_of_nonneg ha hQ.le, le_rfl⟩
  let value (z : ℝ) : ℝ := if hz : z ∈ Icc a 0 then e.pullbackInner z hz x v v else 0
  have hread (z : ℝ) (hz : z ∈ Icc (a / Q) 0) :
      cylinderQuadratic f x v z = Q⁻¹ * value (Q * z) := by
    simp only [cylinderQuadratic, dif_pos hz, value, dif_pos (hmem hz)]
    simpa only [one_div] using Proofs.M47.neck_reclock_pullbackInner e
      (by norm_num) ordConnected_Icc (fun z => Q * z) hmem hmono hclock z hz x v v
  have hbounds := cylinderQuadratic_exp_bounds P hpinch f hU hx v hsQ hzero hsQ.2
    (fun z hz => hfRm z ⟨hsQ.1.trans hz.1, hz.2⟩ x hx)
  have hpower : 6 * (K * Q) * (0 - s / Q) = 6 * K * (-s) := by
    field_simp [hQ.ne']
    ring
  have hnegative : -(6 * (K * Q)) * (0 - s / Q) = -(6 * K * (-s)) := by
    rw [neg_mul, hpower]
  rw [hnegative] at hbounds
  have hback := mul_le_mul_of_nonneg_left hbounds.1 (Real.exp_pos (6 * K * (-s))).le
  have hcancel : Real.exp (6 * K * (-s)) * Real.exp (-(6 * K * (-s))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← mul_assoc, hcancel, one_mul, hread _ hsQ, hread _ hzero,
    mul_div_cancel₀ s hQ.ne', mul_zero] at hback
  have hscaled : Q⁻¹ * value s ≤ Q⁻¹ * (Real.exp (6 * K * (-s)) * value 0) := by
    simpa only [mul_left_comm] using hback
  have h := (mul_le_mul_iff_right₀ (inv_pos.mpr hQ)).mp hscaled
  simpa only [value, dif_pos hs, dif_pos (show (0 : ℝ) ∈ Icc a 0 from ⟨ha, le_rfl⟩)]
    using h

theorem finite_source_metric_exp_upper
    (P : M44CapPersistencePredecessors.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} (hpinch : SurgeryFlowPinched F)
    {base Q a T K : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C base Q (Icc a 0) U) (hU : IsOpen U)
    (ha : a ∈ Icc (-T) 0) (hK : 0 ≤ K)
    (hRm : ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
      (F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs x) ≤ K * Q) :
    ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      e.pullbackInner s hs x v v ≤
        Real.exp (6 * K * T) * e.pullbackInner 0 ⟨ha.2, le_rfl⟩ x v v := by
  intro s hs x hx v
  have hterminal : 0 ≤ e.pullbackInner 0 ⟨ha.2, le_rfl⟩ x v v := by
    unfold SurgeryFlowCylinder.pullbackInner
    apply mul_nonneg e.scale_pos.le
    by_cases hv : mfderiv (𝓡 3) (𝓡 3) (e.forward 0 ⟨ha.2, le_rfl⟩) x v = 0
    · simp only [hv, map_zero, le_refl]
    · exact ((F.metric (base + 0 / Q)).pos _ _ hv).le
  have htime : -s ≤ T := by linarith only [ha.1, hs.1]
  have hfactor : Real.exp (6 * K * (-s)) ≤ Real.exp (6 * K * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime (by positivity))
  exact (normalized_source_metric_exp_upper P hpinch e hU ha.2 hRm s hs x hx v).trans
    (mul_le_mul_of_nonneg_right hfactor hterminal)

end PoincareConjecture.M47
