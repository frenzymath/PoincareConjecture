import PoincareConjecture.Proofs.M47.LimitFiniteForwardScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

private theorem capLineScalar_forward_heq {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (E : SurgeryFlowCylinder F C origin Q I U) {s t : ℝ}
    (hs : s ∈ I) (ht : t ∈ I) (hst : s = t) (x : C.carrier) :
    HEq (E.forward s hs x) (E.forward t ht x) := by
  cases hst
  rfl

private theorem capLineScalar_readout_eq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y := by
  cases hst
  cases hxy
  rfl

theorem finiteHorizon_cap_cylinder_scalar_bound
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    {base Q window r shift a c d L Bold : ℝ}
    (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hwindow : 0 ≤ window) (hScale : 64 * (window + 1) ≤ Q)
    (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
    (hPinched : SurgeryFlowPinched F)
    (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    (P : M44CapPersistencePredecessors.{u})
    {C : GeneralizedSliceCarrier.{u}} {U : Set C.carrier}
    (E : SurgeryFlowCylinder F C (base + shift / Q) Q (Icc a 0) U)
    (hshift : shift ≤ 0) (hd : 0 < d) (hc : c + 2 * d ≤ 0)
    (ha : a ∈ Icc (c - 4 * d) c)
    (hbuffer : -window ≤ shift + c - 4 * d) (hL : 1 ≤ L)
    (hShort : 64 * blowupAnalyticConstant S B * L * (4 * d) ≤ 1)
    (hEndpoint : ∀ x ∈ U,
      (F.connection ((base + shift / Q) + c / Q)).scalarCurvature
        (E.forward c ⟨ha.2, by linarith only [hc, hd]⟩ x) ≤ L * Q)
    (hOld : ∀ s (hs : s ∈ Icc (c + d) 0), ∀ x ∈ U,
      |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
        (E.forward s ⟨by linarith only [hs.1, ha.2, hd], hs.2⟩ x)| ≤ Bold * Q) :
    ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
      (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
        (E.forward s hs x) ≤ max (4 * L) (3 * Bold) * Q := by
  have hQ := E.scale_pos
  have hc0 : c ≤ 0 := by linarith only [hc, hd]
  have hfactor : 0 ≤ 64 * blowupAnalyticConstant S B * L := by
    have hA := blowupAnalyticConstant_pos S B
    have hLp : 0 < L := zero_lt_one.trans_le hL
    positivity
  have haMinus : a - c ≤ 0 := sub_nonpos.mpr ha.2
  have hmemMinus : ∀ v ∈ Icc (a - c) 0, c + v ∈ Icc a 0 := by
    intro v hv
    constructor <;> linarith only [hv.1, hv.2, hc0]
  have hmonoMinus : StrictMonoOn (fun v : ℝ => c + v) (Icc (a - c) 0) := by
    intro v _ w _ hvw
    simpa only [add_comm] using add_lt_add_left hvw c
  have hclockMinus (v : ℝ) (_hv : v ∈ Icc (a - c) 0) :
      (base + (shift + c) / Q) + v / Q = (base + shift / Q) + (c + v) / Q := by
    ring
  let fMinus : SurgeryFlowCylinder F C (base + (shift + c) / Q) Q
      (Icc (a - c) 0) U :=
    Proofs.M47.seedCylinderReclock E hQ ordConnected_Icc
      (fun v => c + v) hmemMinus hmonoMinus hclockMinus
  have hreadMinus (v : ℝ) (hv : v ∈ Icc (a - c) 0)
      (s : ℝ) (hs : s ∈ Icc a 0) (heq : c + v = s) (x : C.carrier) :=
    capLineScalar_readout_eq
      ((hclockMinus v hv).trans
        (congrArg (fun z => (base + shift / Q) + z / Q) heq))
      ((Proofs.M47.seedCylinderReclock_forward_heq E hQ ordConnected_Icc
        (fun v => c + v) hmemMinus hmonoMinus hclockMinus v hv x).trans
        (capLineScalar_forward_heq E _ hs heq x))
  have hterminalMinus (x : C.carrier) (hx : x ∈ U) :
      (F.connection ((base + (shift + c) / Q) + 0 / Q)).scalarCurvature
        (fMinus.forward 0 ⟨haMinus, le_rfl⟩ x) ≤ L * Q := by
    rw [hreadMinus 0 ⟨haMinus, le_rfl⟩ c ⟨ha.2, hc0⟩ (add_zero c) x]
    exact hEndpoint x hx
  have hbufferMinus : -window ≤ (shift + c) + (a - c) := by
    linarith only [hbuffer, ha.1]
  have hshortMinus : 64 * blowupAnalyticConstant S B * L * (-(a - c)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith only [ha.1]) hfactor).trans hShort
  have hpast (s : ℝ) (hs : s ∈ Icc a c) (x : C.carrier) (hx : x ∈ U) :
      (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
        (E.forward s ⟨hs.1, hs.2.trans hc0⟩ x) ≤ 4 * L * Q := by
    have hv : s - c ∈ Icc (a - c) 0 :=
      ⟨sub_le_sub_right hs.1 c, sub_nonpos.mpr hs.2⟩
    have h := limitFinite_shifted_search_scalar_bound S B p O
      hInitial hConstants hC hBase hwindow hScale hLarge hThreshold hPinched hEarlier
      hOverlap P fMinus (add_nonpos hshift hc0) haMinus hbufferMinus hx hL
      (hterminalMinus x hx) hshortMinus (s - c) hv
    rw [hreadMinus (s - c) hv s ⟨hs.1, hs.2.trans hc0⟩ (by ring) x] at h
    exact h
  have haPlus : -2 * d ≤ 0 := by linarith only [hd]
  have hmemPlus : ∀ v ∈ Icc (-2 * d) 0, c + 2 * d + v ∈ Icc a 0 := by
    intro v hv
    constructor <;> linarith only [ha.2, hc, hv.1, hv.2]
  have hmonoPlus : StrictMonoOn (fun v : ℝ => c + 2 * d + v) (Icc (-2 * d) 0) := by
    intro v _ w _ hvw
    simpa only [add_comm] using add_lt_add_left hvw (c + 2 * d)
  have hclockPlus (v : ℝ) (_hv : v ∈ Icc (-2 * d) 0) :
      (base + (shift + c + 2 * d) / Q) + v / Q =
        (base + shift / Q) + (c + 2 * d + v) / Q := by ring
  let fPlus : SurgeryFlowCylinder F C (base + (shift + c + 2 * d) / Q) Q
      (Icc (-2 * d) 0) U :=
    Proofs.M47.seedCylinderReclock E hQ ordConnected_Icc
      (fun v => c + 2 * d + v) hmemPlus hmonoPlus hclockPlus
  have hreadPlus (v : ℝ) (hv : v ∈ Icc (-2 * d) 0)
      (s : ℝ) (hs : s ∈ Icc a 0) (heq : c + 2 * d + v = s) (x : C.carrier) :=
    capLineScalar_readout_eq
      ((hclockPlus v hv).trans
        (congrArg (fun z => (base + shift / Q) + z / Q) heq))
      ((Proofs.M47.seedCylinderReclock_forward_heq E hQ ordConnected_Icc
        (fun v => c + 2 * d + v) hmemPlus hmonoPlus hclockPlus v hv x).trans
        (capLineScalar_forward_heq E _ hs heq x))
  have hbottomPlus (x : C.carrier) (hx : x ∈ U) :
      (F.connection ((base + (shift + c + 2 * d) / Q) + (-2 * d) / Q)).scalarCurvature
        (fPlus.forward (-2 * d) ⟨le_rfl, haPlus⟩ x) ≤ L * Q := by
    rw [hreadPlus (-2 * d) ⟨le_rfl, haPlus⟩ c ⟨ha.2, hc0⟩ (by ring) x]
    exact hEndpoint x hx
  have hshiftPlus : shift + c + 2 * d ≤ 0 := by linarith only [hshift, hc]
  have hbufferPlus : -window ≤ (shift + c + 2 * d) + (-2 * d) := by
    linarith only [hbuffer, hd]
  have hshortPlus : 64 * blowupAnalyticConstant S B * L * (-(-2 * d)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith only [hd]) hfactor).trans hShort
  have hforward (s : ℝ) (hs : s ∈ Icc c (c + 2 * d))
      (x : C.carrier) (hx : x ∈ U) :
      (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
        (E.forward s ⟨ha.2.trans hs.1, hs.2.trans hc⟩ x) ≤ 4 * L * Q := by
    have hv : s - (c + 2 * d) ∈ Icc (-2 * d) 0 := by
      constructor <;> linarith only [hs.1, hs.2]
    have h := limitFinite_shifted_forward_scalar_bound S B p O
      hInitial hConstants hC hBase hwindow hScale hLarge hThreshold hPinched hEarlier
      hOverlap P fPlus hshiftPlus haPlus hbufferPlus hx hL (hbottomPlus x hx)
      hshortPlus (s - (c + 2 * d)) hv
    rw [hreadPlus _ hv s ⟨ha.2.trans hs.1, hs.2.trans hc⟩ (by ring) x] at h
    exact h
  intro s hs x hx
  by_cases hsc : s ≤ c
  · exact (hpast s ⟨hs.1, hsc⟩ x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le)
  · by_cases hsf : s ≤ c + 2 * d
    · exact (hforward s ⟨le_of_not_ge hsc, hsf⟩ x hx).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le)
    · have hsOld : s ∈ Icc (c + d) 0 :=
        ⟨by linarith only [le_of_not_ge hsf, hd], hs.2⟩
      have hnorm : (F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
          (E.forward s hs x) ≤ Bold * Q :=
        (le_abs_self _).trans (hOld s hsOld x hx)
      calc
        _ ≤ 3 * (F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
            (E.forward s hs x) :=
          (F.connection _).scalarCurvature_le_curvatureTensorNorm_sharp _
        _ ≤ 3 * (Bold * Q) := mul_le_mul_of_nonneg_left hnorm (by norm_num)
        _ = (3 * Bold) * Q := (mul_assoc _ _ _).symm
        _ ≤ max (4 * L) (3 * Bold) * Q :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le

end PoincareConjecture.M47
