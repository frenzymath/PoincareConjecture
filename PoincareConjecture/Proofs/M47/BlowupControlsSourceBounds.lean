import PoincareConjecture.Proofs.M47.BlowupControlsFirstFailure
import PoincareConjecture.Proofs.M47.BlowupControlsPinching
import PoincareConjecture.Proofs.M47.SeedCylinderClock
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalarBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46

private theorem scalar_eq_of_heq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y := by
  cases hst
  cases hxy
  rfl

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C)
  (p : SurgeryParameterPrefix S.constants)
  {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
  (hInitial : F.standard_initial = S.setup.standard_initial)
  (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
  {base Q T r : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
  (hT : 0 ≤ T) (hScale : 64 * (T + 1) ≤ Q)
  (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
  (hPinched : SurgeryFlowPinched F)
  (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
  (hOverlap : ∀ u ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
    F.parameters.delta u ≤ B.delta S.setup.standard_initial S.constants)

include hInitial hConstants hC hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap



theorem first_failure_search_scalar_bound
    (P : M44CapPersistencePredecessors.{u})
    {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier} {a L : ℝ}
    (e : SurgeryFlowCylinder F Z base Q (Icc a 0) U)
    (ha : a ≤ 0) (haT : -T ≤ a) {x : Z.carrier} (hx : x ∈ U)
    (hL : 1 ≤ L)
    (hTerminal : (F.connection (base + 0 / Q)).scalarCurvature
      (e.forward 0 ⟨ha, le_rfl⟩ x) ≤ L * Q)
    (hShort : 64 * blowupAnalyticConstant S B * L * (-a) ≤ 1) :
    ∀ s (hs : s ∈ Icc a 0),
      (F.connection (base + s / Q)).scalarCurvature (e.forward s hs x) ≤ 4 * L * Q := by
  have hQ := e.scale_pos
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hLQ : 0 < L * Q := mul_pos hLpos hQ
  have hmem : MapsTo (fun z : ℝ => Q * z) (Icc (a / Q) 0) (Icc a 0) := by
    intro z hz
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hQ).mp hz.1
    · exact mul_nonpos_of_nonneg_of_nonpos hQ.le hz.2
  have hmono : StrictMonoOn (fun z : ℝ => Q * z) (Icc (a / Q) 0) := by
    intro z _ w _ hzw
    exact mul_lt_mul_of_pos_left hzw hQ
  have hclock (z : ℝ) (_hz : z ∈ Icc (a / Q) 0) :
      base + z / 1 = base + (Q * z) / Q := by
    rw [div_one, mul_div_cancel_left₀ z hQ.ne']
  let f : SurgeryFlowCylinder F Z base 1 (Icc (a / Q) 0) U :=
    Proofs.M47.seedCylinderReclock e (by norm_num) ordConnected_Icc
      (fun z => Q * z) hmem hmono hclock
  have hread (z : ℝ) (hz : z ∈ Icc (a / Q) 0) :
      cylinderScalar f x z = cylinderScalar e x (Q * z) := by
    rw [cylinderScalar_of_mem f x z hz, cylinderScalar_of_mem e x (Q * z) (hmem hz)]
    have he := Proofs.M47.seedCylinderReclock_forward_heq e
      (by norm_num) ordConnected_Icc (fun z => Q * z) hmem hmono hclock z hz x
    change HEq (f.forward z hz x) (e.forward (Q * z) (hmem hz) x) at he
    exact scalar_eq_of_heq (hclock z hz) he
  let rho := (Real.sqrt (L * Q))⁻¹
  have hrho : 0 < rho := inv_pos.mpr (Real.sqrt_pos.mpr hLQ)
  have hrhoSq : rho⁻¹ ^ 2 = L * Q := by
    dsimp only [rho]
    rw [inv_inv, Real.sq_sqrt hLQ.le]
  have hzero : (0 : ℝ) ∈ Icc (a / Q) 0 :=
    ⟨div_nonpos_of_nonpos_of_nonneg ha hQ.le, le_rfl⟩
  have hstart : cylinderScalar f x 0 ≤ 2 * rho⁻¹ ^ 2 := by
    rw [hread 0 hzero, mul_zero, cylinderScalar_of_mem e x 0 ⟨ha, le_rfl⟩, hrhoSq]
    exact hTerminal.trans (by linarith only [hLQ])
  have hrate : ∀ z ∈ Ioo (a / Q) 0, base + z / 1 ∉ F.surgery_times →
      rho⁻¹ ^ 2 ≤ cylinderScalar f x z →
        |cylinderScalarRate f x z| ≤ blowupAnalyticConstant S B * cylinderScalar f x z ^ 2 := by
    intro z hz _hnot hhigh
    have hzI := Ioo_subset_Icc_self hz
    have hQle : Q ≤ (F.connection (base + z / 1)).scalarCurvature (f.forward z hzI x) := by
      rw [hrhoSq, cylinderScalar_of_mem f x z hzI] at hhigh
      exact (by nlinarith only [hL, hQ] : Q ≤ L * Q).trans hhigh
    have htime : base + z / 1 ∈ Ico (base - T / Q) base := by
      have hleft := div_le_div_of_nonneg_right haT hQ.le
      rw [neg_div] at hleft
      simp only [mem_Ico, div_one]
      constructor <;> linarith only [hleft, hz.1, hz.2]
    have h := first_failure_physical_analytic_estimate S B p O hInitial hConstants hC
      hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap htime
      (f.forward z hzI x) hQle
    classical
    simpa only [cylinderScalar, cylinderScalarRate, dif_pos hzI] using h.2.2
  have hshort : 64 * blowupAnalyticConstant S B * rho⁻¹ ^ 2 * (-(a / Q)) ≤ 1 := by
    rw [hrhoSq]
    have heq : 64 * blowupAnalyticConstant S B * (L * Q) * (-(a / Q)) =
        64 * blowupAnalyticConstant S B * L * (-a) := by
      field_simp [hQ.ne']
    rw [heq]
    exact hShort
  have hbound := cylinderScalar_le_four_inv_sq P hPinched f hx hzero.1
    (blowupAnalyticConstant_pos S B) hrho hstart hrate hshort
  intro s hs
  have hs' : s / Q ∈ Icc (a / Q) 0 :=
    ⟨div_le_div_of_nonneg_right hs.1 hQ.le, div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le⟩
  have h := hbound (s / Q) hs'
  have hcancel : Q * (s / Q) = s := by field_simp
  rw [hread (s / Q) hs', hcancel, cylinderScalar_of_mem e x s hs, hrhoSq] at h
  simpa only [mul_assoc] using h



theorem first_failure_search_curvature_bounds
    (P : M46Predecessors.{u})
    {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier} {a L eta : ℝ}
    (e : SurgeryFlowCylinder F Z base Q (Icc a 0) U)
    (ha : a ≤ 0) (haT : -T ≤ a) {x : Z.carrier} (hx : x ∈ U)
    (hL : 1 ≤ L)
    (hTerminal : (F.connection (base + 0 / Q)).scalarCurvature
      (e.forward 0 ⟨ha, le_rfl⟩ x) ≤ L * Q)
    (hShort : 64 * blowupAnalyticConstant S B * L * (-a) ≤ 1)
    (heta : 0 < eta) (hPinchingScale : blowupPinchingThreshold (4 * L) eta ≤ Q) :
    ∀ s (hs : s ∈ Icc a 0),
      |(F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs x)| ≤
          (13 * max (4 * L) 1) * Q ∧
        (F.connection (base + s / Q)).negativeCurvaturePart (e.forward s hs x) ≤ eta * Q := by
  have hscalar := first_failure_search_scalar_bound S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
    ⟨P.m04, P.m13.ordinary_flow⟩ e ha haT hx hL hTerminal hShort
  intro s hs
  apply pinched_blowup_curvature_bounds P
    (hPinched _ (e.time_subset (mem_image_of_mem _ hs))) (by linarith only [hL])
    heta hPinchingScale (mem_univ _)
  exact hscalar s hs

end PoincareConjecture.M47
