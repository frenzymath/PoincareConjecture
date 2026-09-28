import PoincareConjecture.Proofs.M47.LimitFinitePreservedBounds
import PoincareConjecture.Proofs.M47.LimitFiniteForwardScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

private theorem uniform_forward_heq {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin Q I U) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (hst : s = t) (x : C.carrier) : HEq (e.forward s hs x) (e.forward t ht x) := by
  cases hst
  rfl

private theorem uniform_readout_eq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y ∧
      (F.connection s).curvatureTensorNorm x = (F.connection t).curvatureTensorNorm y ∧
      (F.connection s).negativeCurvaturePart x = (F.connection t).negativeCurvaturePart y := by
  cases hst
  cases hxy
  exact ⟨rfl, rfl, rfl⟩



theorem limitFinite_exists_uniform_preserved_search
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    {base Q window r shift c d L Bold eta : ℝ}
    (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hwindow : 0 ≤ window) (hScale : 64 * (window + 1) ≤ Q)
    (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
    (hPinched : SurgeryFlowPinched F)
    (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    (P : M46Predecessors.{u}) {C : GeneralizedSliceCarrier.{u}} {U : Set C.carrier}
    (e0 : SurgeryFlowCylinder F C (base + shift / Q) Q (Icc c 0) U)
    (hshift : shift ≤ 0) (hd : 0 < d) (hc : c + 2 * d ≤ 0)
    (hbuffer : -window ≤ shift + c - 4 * d) (hL : 1 ≤ L)
    (hShort : 64 * blowupAnalyticConstant S B * L * (4 * d) ≤ 1)
    (hU : IsOpen U) (hne : U.Nonempty)
    (hEndpoint : ∀ x ∈ U,
      (F.connection ((base + shift / Q) + c / Q)).scalarCurvature
        (e0.forward c ⟨le_rfl, by linarith only [hc, hd]⟩ x) ≤ L * Q)
    (heta : 0 < eta) (hPinchingScale : blowupPinchingThreshold (4 * L) eta ≤ Q)
    (hOld : ∀ s (hs : s ∈ Icc (c + d) 0), ∀ x ∈ U,
      |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
        (e0.forward s ⟨by linarith only [hs.1, hd], hs.2⟩ x)| ≤ Bold * Q ∧
      (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
        (e0.forward s ⟨by linarith only [hs.1, hd], hs.2⟩ x) ≤ eta * Q) :
    ∃ (b : ℝ) (hb : b ∈ Icc (c - 4 * d) c),
      ∃ E : SurgeryFlowCylinder F C (base + shift / Q) Q (Icc b 0) U,
        (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0) x,
          E.forward s hs' x = e0.forward s hs x) ∧
        (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
          |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
            (E.forward s hs x)| ≤ max (13 * max (4 * L) 1) Bold * Q ∧
          (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
            (E.forward s hs x) ≤ eta * Q) ∧
        (b < c - 2 * d ∨ b ∈ Icc (c - 2 * d) c ∧
          ∃ hEvent : (base + shift / Q) + b / Q ∈ F.surgery_times,
            ∀ [Nonempty (F.slice ((base + shift / Q) + b / Q)).carrier],
              ∃ i : Fin (F.event ((base + shift / Q) + b / Q) hEvent).cap_count,
                (E.forward b ⟨le_rfl, by linarith only [hb.2, hc, hd]⟩ '' U ∩
                  ((F.event ((base + shift / Q) + b / Q) hEvent).caps i).carrier).Nonempty) := by
  have hQ := e0.scale_pos
  have hc0 : c ≤ 0 := by linarith only [hc, hd]
  have hbuffer' : -window ≤ shift + c - 2 * (2 * d) := by
    nlinarith only [hbuffer]
  have hshort' : 64 * blowupAnalyticConstant S B * L * (2 * (2 * d)) ≤ 1 := by
    nlinarith only [hShort]
  obtain ⟨b, hb, E, hfuture, hpast, hstop⟩ := limitFinite_exists_preserved_bounded_search
    S B p O hInitial hConstants hC hBase hwindow hScale hLarge hThreshold
    hPinched hEarlier hOverlap P e0 hshift hc0 (mul_pos two_pos hd)
    hbuffer' hL hshort' hU hne hEndpoint heta hPinchingScale
  have hb' : b ∈ Icc (c - 4 * d) c := by
    constructor <;> linarith only [hb.1, hb.2]
  have hmem : ∀ u ∈ Icc (-2 * d) 0, c + 2 * d + u ∈ Icc b 0 := by
    intro u hu
    constructor <;> linarith only [hb.2, hc, hu.1, hu.2]
  have hmono : StrictMonoOn (fun u : ℝ => c + 2 * d + u) (Icc (-2 * d) 0) := by
    intro u _ v _ huv
    simpa only [add_comm] using add_lt_add_left huv (c + 2 * d)
  have hclock (u : ℝ) (_hu : u ∈ Icc (-2 * d) 0) :
      (base + (shift + c + 2 * d) / Q) + u / Q =
        (base + shift / Q) + (c + 2 * d + u) / Q := by ring
  let f : SurgeryFlowCylinder F C (base + (shift + c + 2 * d) / Q) Q
      (Icc (-2 * d) 0) U :=
    Proofs.M47.seedCylinderReclock E hQ ordConnected_Icc
      (fun u => c + 2 * d + u) hmem hmono hclock
  have hread (u : ℝ) (hu : u ∈ Icc (-2 * d) 0)
      (s : ℝ) (hs : s ∈ Icc b 0) (heq : c + 2 * d + u = s) (x : C.carrier) :=
    uniform_readout_eq
      ((hclock u hu).trans (congrArg (fun z => (base + shift / Q) + z / Q) heq))
      ((Proofs.M47.seedCylinderReclock_forward_heq E hQ ordConnected_Icc
        (fun u => c + 2 * d + u) hmem hmono hclock u hu x).trans
        (uniform_forward_heq E _ hs heq x))
  have ha : -2 * d ≤ 0 := by linarith only [hd]
  have hbottom (x : C.carrier) (hx : x ∈ U) :
      (F.connection ((base + (shift + c + 2 * d) / Q) + (-2 * d) / Q)).scalarCurvature
        (f.forward (-2 * d) ⟨le_rfl, ha⟩ x) ≤ L * Q := by
    rw [(hread (-2 * d) ⟨le_rfl, ha⟩ c ⟨hb.2, hc0⟩ (by ring) x).1]
    rw [hfuture c ⟨le_rfl, hc0⟩ _ x]
    exact hEndpoint x hx
  have hshift' : shift + c + 2 * d ≤ 0 := by linarith only [hshift, hc]
  have hbufferF : -window ≤ (shift + c + 2 * d) + (-2 * d) := by
    linarith only [hbuffer, hd]
  have hshortF : 64 * blowupAnalyticConstant S B * L * (-(-2 * d)) ≤ 1 := by
    apply le_trans _ hShort
    apply mul_le_mul_of_nonneg_left (by linarith only [hd])
    have hA := blowupAnalyticConstant_pos S B
    have hLp : 0 ≤ L := zero_le_one.trans hL
    positivity
  have hforward (s : ℝ) (hs : s ∈ Icc c (c + 2 * d)) (x : C.carrier) (hx : x ∈ U) :
      |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
        (E.forward s ⟨hb.2.trans hs.1, hs.2.trans hc⟩ x)| ≤ (13 * max (4 * L) 1) * Q ∧
      (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
        (E.forward s ⟨hb.2.trans hs.1, hs.2.trans hc⟩ x) ≤ eta * Q := by
    have hu : s - (c + 2 * d) ∈ Icc (-2 * d) 0 := by
      constructor <;> linarith only [hs.1, hs.2]
    have h := limitFinite_shifted_forward_curvature_bounds S B p O
      hInitial hConstants hC hBase hwindow hScale hLarge hThreshold hPinched hEarlier
      hOverlap P f hshift' ha hbufferF hx hL (hbottom x hx) hshortF heta hPinchingScale
      (s - (c + 2 * d)) hu
    have hread' := hread _ hu s ⟨hb.2.trans hs.1, hs.2.trans hc⟩ (by ring) x
    rw [hread'.2.1, hread'.2.2] at h
    exact h
  refine ⟨b, hb', E, hfuture, ?_, hstop⟩
  intro s hs x hx
  by_cases hsc : s ≤ c
  · obtain ⟨_hscalar, hnorm, hneg⟩ := hpast s ⟨hs.1, hsc⟩ x hx
    exact ⟨hnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le), hneg⟩
  · by_cases hsf : s ≤ c + 2 * d
    · obtain ⟨hnorm, hneg⟩ := hforward s ⟨le_of_not_ge hsc, hsf⟩ x hx
      exact ⟨hnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le), hneg⟩
    · have hsOld : s ∈ Icc (c + d) 0 :=
        ⟨by linarith only [le_of_not_ge hsf, hd], hs.2⟩
      rw [hfuture s ⟨by linarith only [hsOld.1, hd], hs.2⟩ hs x]
      obtain ⟨hnorm, hneg⟩ := hOld s hsOld x hx
      exact ⟨hnorm.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le), hneg⟩

end PoincareConjecture.M47
