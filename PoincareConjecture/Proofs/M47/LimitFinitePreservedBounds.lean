import PoincareConjecture.Proofs.M47.LimitFinitePreservedSearch
import PoincareConjecture.Proofs.M47.LimitNoncollapseShiftedSearchExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

private theorem preserved_forward_heq {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin Q I U) {s t : ℝ}
    (hs : s ∈ I) (ht : t ∈ I) (hst : s = t) (x : C.carrier) :
    HEq (e.forward s hs x) (e.forward t ht x) := by
  cases hst
  rfl

private theorem preserved_readout_eq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y ∧
      (F.connection s).curvatureTensorNorm x = (F.connection t).curvatureTensorNorm y ∧
      (F.connection s).negativeCurvaturePart x = (F.connection t).negativeCurvaturePart y := by
  cases hst
  cases hxy
  exact ⟨rfl, rfl, rfl⟩

theorem limitFinite_exists_preserved_bounded_search
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    {base Q T r shift c d L eta : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hT : 0 ≤ T) (hScale : 64 * (T + 1) ≤ Q)
    (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
    (hPinched : SurgeryFlowPinched F)
    (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    (P : M46Predecessors.{u}) {C : GeneralizedSliceCarrier.{u}} {U : Set C.carrier}
    (e0 : SurgeryFlowCylinder F C (base + shift / Q) Q (Icc c 0) U)
    (hshift : shift ≤ 0) (hc : c ≤ 0) (hd : 0 < d)
    (hbuffer : -T ≤ shift + c - 2 * d) (hL : 1 ≤ L)
    (hShort : 64 * blowupAnalyticConstant S B * L * (2 * d) ≤ 1)
    (hU : IsOpen U) (hne : U.Nonempty)
    (hTerminal : ∀ x ∈ U,
      (F.connection ((base + shift / Q) + c / Q)).scalarCurvature
        (e0.forward c ⟨le_rfl, hc⟩ x) ≤ L * Q)
    (heta : 0 < eta) (hPinchingScale : blowupPinchingThreshold (4 * L) eta ≤ Q) :
    ∃ (b : ℝ) (hb : b ∈ Icc (c - 2 * d) c),
      ∃ E : SurgeryFlowCylinder F C (base + shift / Q) Q (Icc b 0) U,
        (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0) x,
          E.forward s hs' x = e0.forward s hs x) ∧
        (∀ s (hs : s ∈ Icc b c), ∀ x ∈ U,
          (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
            (E.forward s ⟨hs.1, hs.2.trans hc⟩ x) ≤ 4 * L * Q ∧
          |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
            (E.forward s ⟨hs.1, hs.2.trans hc⟩ x)| ≤ (13 * max (4 * L) 1) * Q ∧
          (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
            (E.forward s ⟨hs.1, hs.2.trans hc⟩ x) ≤ eta * Q) ∧
        (b < c - d ∨ b ∈ Icc (c - d) c ∧
          ∃ hEvent : (base + shift / Q) + b / Q ∈ F.surgery_times,
            ∀ [Nonempty (F.slice ((base + shift / Q) + b / Q)).carrier],
              ∃ i : Fin (F.event ((base + shift / Q) + b / Q) hEvent).cap_count,
                (E.forward b ⟨le_rfl, hb.2.trans hc⟩ '' U ∩
                  ((F.event ((base + shift / Q) + b / Q) hEvent).caps i).carrier).Nonempty) := by
  have hQ := e0.scale_pos
  have hwindow : Icc ((base + shift / Q) + (c - 2 * d) / Q)
      ((base + shift / Q) + c / Q) ⊆ F.time_domain := by
    apply Subset.trans _ (terminalCommonInterval_search_window p O hBase hT hScale)
    have hlower := div_le_div_of_nonneg_right hbuffer hQ.le
    rw [neg_div, sub_div, add_div] at hlower
    have hshiftQ := div_nonpos_of_nonpos_of_nonneg hshift hQ.le
    have hcQ := div_nonpos_of_nonpos_of_nonneg hc hQ.le
    intro s hs
    rw [sub_div] at hs
    constructor <;> linarith only [hlower, hshiftQ, hcQ, hs.1, hs.2]
  obtain ⟨b, hb, E, hfuture, hstop⟩ := limitFinite_exists_preserved_search e0 hc
    (by linarith only [hd] : c - 2 * d ≤ c) hwindow hU hne
  have hbc : b - c ≤ 0 := sub_nonpos.mpr hb.2
  have hmem : ∀ u ∈ Icc (b - c) 0, c + u ∈ Icc b 0 := by
    intro u hu
    constructor <;> linarith only [hu.1, hu.2, hc]
  have hmono : StrictMonoOn (fun u : ℝ => c + u) (Icc (b - c) 0) := by
    intro u _ v _ huv
    simpa only [add_comm] using add_lt_add_left huv c
  have hclock (u : ℝ) (_hu : u ∈ Icc (b - c) 0) :
      (base + (shift + c) / Q) + u / Q = (base + shift / Q) + (c + u) / Q := by
    ring
  let f : SurgeryFlowCylinder F C (base + (shift + c) / Q) Q (Icc (b - c) 0) U :=
    Proofs.M47.seedCylinderReclock E hQ ordConnected_Icc
      (fun u => c + u) hmem hmono hclock
  have hread (u : ℝ) (hu : u ∈ Icc (b - c) 0)
      (s : ℝ) (hs : s ∈ Icc b 0) (hparam : c + u = s) (x : C.carrier) :=
    preserved_readout_eq
      ((hclock u hu).trans (congrArg (fun z => (base + shift / Q) + z / Q) hparam))
      ((Proofs.M47.seedCylinderReclock_forward_heq E hQ ordConnected_Icc
        (fun u => c + u) hmem hmono hclock u hu x).trans
        (preserved_forward_heq E _ hs hparam x))
  have hceiling (x : C.carrier) (hx : x ∈ U) :
      (F.connection ((base + (shift + c) / Q) + 0 / Q)).scalarCurvature
        (f.forward 0 ⟨hbc, le_rfl⟩ x) ≤ L * Q := by
    rw [(hread 0 ⟨hbc, le_rfl⟩ c ⟨hb.2, hc⟩ (add_zero c) x).1]
    rw [hfuture c ⟨le_rfl, hc⟩ _ x]
    exact hTerminal x hx
  have hbuffer' : -T ≤ (shift + c) + (b - c) := by linarith [hb.1]
  have hshort : 64 * blowupAnalyticConstant S B * L * (-(b - c)) ≤ 1 := by
    apply le_trans _ hShort
    apply mul_le_mul_of_nonneg_left (by linarith [hb.1])
    have := blowupAnalyticConstant_pos S B
    positivity
  have hshift' : shift + c ≤ 0 := add_nonpos hshift hc
  refine ⟨b, hb, E, hfuture, ?_, ?_⟩
  · intro s hs x hx
    have hs' : s - c ∈ Icc (b - c) 0 :=
      ⟨sub_le_sub_right hs.1 c, sub_nonpos.mpr hs.2⟩
    have hscalar := limitFinite_shifted_search_scalar_bound S B p O
      hInitial hConstants hC hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
      ⟨P.m04, P.m13.ordinary_flow⟩ f hshift' hbc hbuffer' hx hL (hceiling x hx) hshort
      (s - c) hs'
    have hcurvature := limitFinite_shifted_search_curvature_bounds S B p O
      hInitial hConstants hC hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
      P f hshift' hbc hbuffer' hx hL (hceiling x hx) hshort heta hPinchingScale
      (s - c) hs'
    have hidentity : c + (s - c) = s := by ring
    have hread' := hread (s - c) hs' s ⟨hs.1, hs.2.trans hc⟩ hidentity x
    rw [hread'.1] at hscalar
    rw [hread'.2.1, hread'.2.2] at hcurvature
    exact ⟨hscalar, hcurvature⟩
  · by_cases hlong : b < c - d
    · exact Or.inl hlong
    · refine Or.inr ⟨⟨le_of_not_gt hlong, hb.2⟩, hstop.resolve_left ?_⟩
      intro heq
      exact hlong (by rw [heq]; linarith only [hd])

end PoincareConjecture.M47
