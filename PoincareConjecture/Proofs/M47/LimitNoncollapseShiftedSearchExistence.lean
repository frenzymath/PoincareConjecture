import PoincareConjecture.Proofs.M47.LimitNoncollapseShiftedSearch
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSearch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

private theorem shifted_initial_scalar_eq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y := by
  cases hst
  cases hxy
  rfl

theorem limitFinite_exists_shifted_bounded_search
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    {base Q T r shift d L eta : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hT : 0 ≤ T) (hScale : 64 * (T + 1) ≤ Q)
    (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
    (hPinched : SurgeryFlowPinched F)
    (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ u ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta u ≤ B.delta S.setup.standard_initial S.constants)
    (P : M46Predecessors.{u}) (hshift : shift ≤ 0) (hd : 0 < d)
    (hbuffer : -T ≤ shift - 2 * d) (hL : 1 ≤ L)
    (hShort : 64 * blowupAnalyticConstant S B * L * (2 * d) ≤ 1)
    (U : Set (F.slice (base + shift / Q)).carrier) (hU : IsOpen U) (hne : U.Nonempty)
    (hTerminal : ∀ x ∈ U, (F.connection (base + shift / Q)).scalarCurvature x ≤ L * Q)
    (heta : 0 < eta) (hPinchingScale : blowupPinchingThreshold (4 * L) eta ≤ Q) :
    ∃ (a : ℝ) (ha : a ∈ Icc (-2 * d) 0),
      ∃ e : SurgeryFlowCylinder F (F.slice (base + shift / Q))
        (base + shift / Q) Q (Icc a 0) U,
        (∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x) ∧
        (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
          (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
            (e.forward s hs x) ≤ 4 * L * Q ∧
          |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
            (e.forward s hs x)| ≤ (13 * max (4 * L) 1) * Q ∧
          (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
            (e.forward s hs x) ≤ eta * Q) ∧
        (a < -d ∨ a ∈ Icc (-d) 0 ∧
          ∃ hEvent : (base + shift / Q) + a / Q ∈ F.surgery_times,
            ∀ [Nonempty (F.slice ((base + shift / Q) + a / Q)).carrier],
              ∃ i : Fin (F.event ((base + shift / Q) + a / Q) hEvent).cap_count,
                (e.forward a ⟨le_rfl, ha.2⟩ '' U ∩
                  ((F.event ((base + shift / Q) + a / Q) hEvent).caps i).carrier).Nonempty) := by
  have hQ : 0 < Q := by linarith
  have hwindow : Icc ((base + shift / Q) + (-2 * d) / Q) (base + shift / Q) ⊆
      F.time_domain := by
    apply Subset.trans _ (terminalCommonInterval_search_window p O hBase hT hScale)
    have hlower := div_le_div_of_nonneg_right hbuffer hQ.le
    rw [neg_div, sub_div] at hlower
    have hupper := div_nonpos_of_nonpos_of_nonneg hshift hQ.le
    intro s hs
    simp only [neg_mul, neg_div] at hs
    constructor <;> linarith only [hlower, hupper, hs.1, hs.2]
  obtain ⟨a, ha, e, hbased, hstop⟩ := exists_normalized_open_region_search F hQ
    (by linarith only [hd] : -2 * d ≤ 0) hwindow U hU hne
  have hceiling : ∀ x ∈ U, (F.connection ((base + shift / Q) + 0 / Q)).scalarCurvature
      (e.forward 0 ⟨ha.2, le_rfl⟩ x) ≤ L * Q := by
    intro x hx
    rw [shifted_initial_scalar_eq (by simp) (hbased _ x hx)]
    exact hTerminal x hx
  have hbuffer' : -T ≤ shift + a := by linarith [ha.1]
  have hshort : 64 * blowupAnalyticConstant S B * L * (-a) ≤ 1 := by
    apply le_trans _ hShort
    apply mul_le_mul_of_nonneg_left (by linarith [ha.1])
    have := blowupAnalyticConstant_pos S B
    positivity
  refine ⟨a, ha, e, hbased, ?_, ?_⟩
  · intro s hs x hx
    exact ⟨limitFinite_shifted_search_scalar_bound S B p O hInitial hConstants hC
      hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
      ⟨P.m04, P.m13.ordinary_flow⟩ e hshift ha.2 hbuffer' hx hL (hceiling x hx) hshort s hs,
      limitFinite_shifted_search_curvature_bounds S B p O hInitial hConstants hC
        hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
        P e hshift ha.2 hbuffer' hx hL (hceiling x hx) hshort heta hPinchingScale s hs⟩
  · by_cases hlong : a < -d
    · exact Or.inl hlong
    · refine Or.inr ⟨⟨le_of_not_gt hlong, ha.2⟩, hstop.resolve_left ?_⟩
      intro heq
      exact hlong (by rw [heq]; linarith only [hd])

end PoincareConjecture.M47
