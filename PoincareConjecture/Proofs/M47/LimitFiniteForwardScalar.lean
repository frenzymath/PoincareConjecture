import PoincareConjecture.Proofs.M47.LimitNoncollapseShiftedSearch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem limitFinite_cylinder_scalar_forward
    {F : SurgeryFlowData.{u}} {Z : GeneralizedSliceCarrier.{u}}
    {origin c : ℝ} {U : Set Z.carrier}
    (P : M44CapPersistencePredecessors.{u}) (hPinched : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F Z origin 1 (Icc c 0) U)
    {x : Z.carrier} (hx : x ∈ U) (hc : c ≤ 0) {A rho : ℝ}
    (hA : 0 < A) (hrho : 0 < rho)
    (hInitial : cylinderScalar e x c ≤ 2 * rho⁻¹ ^ 2)
    (hRate : ∀ s ∈ Ioo c 0, origin + s / 1 ∉ F.surgery_times →
      rho⁻¹ ^ 2 ≤ cylinderScalar e x s →
        |cylinderScalarRate e x s| ≤ A * cylinderScalar e x s ^ 2)
    (hShort : 64 * A * rho⁻¹ ^ 2 * (-c) ≤ 1) :
    ∀ s ∈ Icc c 0, cylinderScalar e x s ≤ 4 * rho⁻¹ ^ 2 := by
  let f : ℝ → ℝ := fun t => cylinderScalar e x (c + t)
  let rate : ℝ → ℝ := fun t => cylinderScalarRate e x (c + t)
  let events : Set ℝ := (fun t : ℝ => origin + c + t) ⁻¹' F.surgery_times
  have htime : Icc (origin + c) origin ⊆ F.time_domain := by
    apply F.time_domain_interval.out
    · simpa only [div_one] using
        e.time_subset (mem_image_of_mem _ (show c ∈ Icc c 0 from ⟨le_rfl, hc⟩))
    · simpa only [zero_div, add_zero] using
        e.time_subset (mem_image_of_mem _ (show 0 ∈ Icc c 0 from ⟨hc, le_rfl⟩))
  have hfinite : (events ∩ Ioc 0 (-c)).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc htime
    have hinj : Function.Injective (fun t : ℝ => origin + c + t) :=
      fun _ _ h => by linarith
    apply (hf.preimage hinj.injOn).subset
    intro t ht
    exact ⟨ht.1, by dsimp only [mem_Icc]; constructor <;> linarith [ht.2.1, ht.2.2]⟩
  have hcont : ContinuousOn f (Icc 0 (-c)) :=
    (cylinderScalar_continuousOn P hPinched e hx).comp
      (continuous_const.add continuous_id).continuousOn
      (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hderiv : ∀ t ∈ Ioo 0 (-c), t ∉ events → HasDerivAt f (rate t) t := by
    intro t ht hnot
    have hs : c + t ∈ Ioo c 0 := by constructor <;> linarith [ht.1, ht.2]
    have hnot' : origin + (c + t) / 1 ∉ F.surgery_times := by
      simpa only [events, mem_preimage, div_one, add_assoc] using hnot
    have h := (cylinderScalar_hasDerivAt_of_not_surgery P e hx hs hnot').comp t
      ((hasDerivAt_const t c).add (hasDerivAt_id t))
    simpa only [f, rate, Function.comp_def, div_one, zero_add, mul_one] using h
  have hrate : ∀ t ∈ Ioo 0 (-c), t ∉ events →
      rho⁻¹ ^ 2 ≤ f t → rate t ≤ A * f t ^ 2 := by
    intro t ht hnot hhigh
    have hs : c + t ∈ Ioo c 0 := by constructor <;> linarith [ht.1, ht.2]
    have hnot' : origin + (c + t) / 1 ∉ F.surgery_times := by
      simpa only [events, mem_preimage, div_one, add_assoc] using hnot
    exact (le_abs_self _).trans (hRate (c + t) hs hnot' hhigh)
  have hbound := scalar_le_four_inv_sq_of_finite_events hA hrho hfinite hcont hderiv
    (by simpa only [f, add_zero] using hInitial) hrate hShort
  intro s hs
  have hclock : c + (s - c) = s := by ring
  simpa only [f, hclock] using
    hbound (s - c) (by constructor <;> linarith [hs.1, hs.2])

private theorem forward_scalar_eq_of_heq {F : SurgeryFlowData.{u}} {s t : ℝ}
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
  (hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
    F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)

include hInitial hConstants hC hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap

theorem limitFinite_shifted_forward_scalar_bound
    (P : M44CapPersistencePredecessors.{u})
    {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier} {shift a L : ℝ}
    (e : SurgeryFlowCylinder F Z (base + shift / Q) Q (Icc a 0) U)
    (hshift : shift ≤ 0) (ha : a ≤ 0) (hbuffer : -T ≤ shift + a)
    {x : Z.carrier} (hx : x ∈ U) (hL : 1 ≤ L)
    (hBottom : (F.connection ((base + shift / Q) + a / Q)).scalarCurvature
      (e.forward a ⟨le_rfl, ha⟩ x) ≤ L * Q)
    (hShort : 64 * blowupAnalyticConstant S B * L * (-a) ≤ 1) :
    ∀ s (hs : s ∈ Icc a 0),
      (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
        (e.forward s hs x) ≤ 4 * L * Q := by
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
      (base + shift / Q) + z / 1 = (base + shift / Q) + (Q * z) / Q := by
    rw [div_one, mul_div_cancel_left₀ z hQ.ne']
  let f : SurgeryFlowCylinder F Z (base + shift / Q) 1 (Icc (a / Q) 0) U :=
    Proofs.M47.seedCylinderReclock e (by norm_num) ordConnected_Icc
      (fun z => Q * z) hmem hmono hclock
  have hread (z : ℝ) (hz : z ∈ Icc (a / Q) 0) :
      cylinderScalar f x z = cylinderScalar e x (Q * z) := by
    rw [cylinderScalar_of_mem f x z hz, cylinderScalar_of_mem e x (Q * z) (hmem hz)]
    exact forward_scalar_eq_of_heq (hclock z hz)
      (Proofs.M47.seedCylinderReclock_forward_heq e
        (by norm_num) ordConnected_Icc (fun z => Q * z) hmem hmono hclock z hz x)
  let rho := (Real.sqrt (L * Q))⁻¹
  have hrho : 0 < rho := inv_pos.mpr (Real.sqrt_pos.mpr hLQ)
  have hrhoSq : rho⁻¹ ^ 2 = L * Q := by
    dsimp only [rho]
    rw [inv_inv, Real.sq_sqrt hLQ.le]
  have haQ : a / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha hQ.le
  have hstart : cylinderScalar f x (a / Q) ≤ 2 * rho⁻¹ ^ 2 := by
    have hcancel : Q * (a / Q) = a := by field_simp
    rw [hread (a / Q) ⟨le_rfl, haQ⟩, hcancel,
      cylinderScalar_of_mem e x a ⟨le_rfl, ha⟩, hrhoSq]
    exact hBottom.trans (by linarith only [hLQ])
  have hrate : ∀ z ∈ Ioo (a / Q) 0,
      (base + shift / Q) + z / 1 ∉ F.surgery_times →
      rho⁻¹ ^ 2 ≤ cylinderScalar f x z →
        |cylinderScalarRate f x z| ≤ blowupAnalyticConstant S B * cylinderScalar f x z ^ 2 := by
    intro z hz _hnot hhigh
    have hzI := Ioo_subset_Icc_self hz
    have hQle : Q ≤ (F.connection ((base + shift / Q) + z / 1)).scalarCurvature
        (f.forward z hzI x) := by
      rw [hrhoSq, cylinderScalar_of_mem f x z hzI] at hhigh
      exact (by nlinarith only [hL, hQ] : Q ≤ L * Q).trans hhigh
    have htime : (base + shift / Q) + z / 1 ∈ Ico (base - T / Q) base := by
      have hleft := div_le_div_of_nonneg_right hbuffer hQ.le
      rw [neg_div, add_div] at hleft
      have hright := div_nonpos_of_nonpos_of_nonneg hshift hQ.le
      simp only [mem_Ico, div_one]
      constructor <;> linarith only [hleft, hright, hz.1, hz.2]
    have h := first_failure_physical_analytic_estimate S B p O hInitial hConstants hC
      hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap htime
      (f.forward z hzI x) hQle
    classical
    simpa only [cylinderScalar, cylinderScalarRate, dif_pos hzI] using h.2.2
  have hshort : 64 * blowupAnalyticConstant S B * rho⁻¹ ^ 2 * (-(a / Q)) ≤ 1 := by
    rw [hrhoSq]
    have heq : 64 * blowupAnalyticConstant S B * (L * Q) * (-(a / Q)) =
        64 * blowupAnalyticConstant S B * L * (-a) := by field_simp [hQ.ne']
    rw [heq]
    exact hShort
  have hbound := limitFinite_cylinder_scalar_forward P hPinched f hx haQ
    (blowupAnalyticConstant_pos S B) hrho hstart hrate hshort
  intro s hs
  have hs' : s / Q ∈ Icc (a / Q) 0 :=
    ⟨div_le_div_of_nonneg_right hs.1 hQ.le, div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le⟩
  have h := hbound (s / Q) hs'
  have hcancel : Q * (s / Q) = s := by field_simp
  rw [hread (s / Q) hs', hcancel, cylinderScalar_of_mem e x s hs, hrhoSq] at h
  simpa only [mul_assoc] using h

theorem limitFinite_shifted_forward_curvature_bounds
    (P : M46Predecessors.{u})
    {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier} {shift a L eta : ℝ}
    (e : SurgeryFlowCylinder F Z (base + shift / Q) Q (Icc a 0) U)
    (hshift : shift ≤ 0) (ha : a ≤ 0) (hbuffer : -T ≤ shift + a)
    {x : Z.carrier} (hx : x ∈ U) (hL : 1 ≤ L)
    (hBottom : (F.connection ((base + shift / Q) + a / Q)).scalarCurvature
      (e.forward a ⟨le_rfl, ha⟩ x) ≤ L * Q)
    (hShort : 64 * blowupAnalyticConstant S B * L * (-a) ≤ 1)
    (heta : 0 < eta) (hPinchingScale : blowupPinchingThreshold (4 * L) eta ≤ Q) :
    ∀ s (hs : s ∈ Icc a 0),
      |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
        (e.forward s hs x)| ≤ (13 * max (4 * L) 1) * Q ∧
      (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
        (e.forward s hs x) ≤ eta * Q := by
  have hscalar := limitFinite_shifted_forward_scalar_bound S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
    ⟨P.m04, P.m13.ordinary_flow⟩ e hshift ha hbuffer hx hL hBottom hShort
  intro s hs
  apply pinched_blowup_curvature_bounds P
    (hPinched _ (e.time_subset (mem_image_of_mem _ hs))) (by linarith only [hL])
    heta hPinchingScale (mem_univ _)
  exact hscalar s hs

end PoincareConjecture.M47
