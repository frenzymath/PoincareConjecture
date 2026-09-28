import PoincareConjecture.Proofs.M47.BlowupControlsSourceBounds
import PoincareConjecture.Proofs.M47.BlowupControlsSequence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47


noncomputable def terminalCommonIntervalDuration
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) (K : ℝ) : ℝ :=
  (256 * blowupAnalyticConstant S B * (2 * K))⁻¹


theorem terminalCommonInterval_duration_bounds
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) {K : ℝ} (hK : 1 ≤ K) :
    0 < terminalCommonIntervalDuration S B K ∧
      terminalCommonIntervalDuration S B K ≤ 1 ∧
      64 * blowupAnalyticConstant S B * (2 * K) *
        (2 * terminalCommonIntervalDuration S B K) ≤ 1 := by
  have hA : 1 ≤ blowupAnalyticConstant S B := le_max_left _ _
  have hApos := blowupAnalyticConstant_pos S B
  have hL : 1 ≤ 2 * K := by linarith
  have hLpos : 0 < 2 * K := by linarith
  have hprod : 1 ≤ blowupAnalyticConstant S B * (2 * K) := by
    simpa only [one_mul] using mul_le_mul hA hL zero_le_one hApos.le
  have hden : 0 < 256 * blowupAnalyticConstant S B * (2 * K) := by positivity
  refine ⟨inv_pos.mpr hden, (inv_le_one₀ hden).mpr (by nlinarith), ?_⟩
  have heq : 64 * blowupAnalyticConstant S B * (2 * K) *
      (2 * terminalCommonIntervalDuration S B K) = 1 / 2 := by
    unfold terminalCommonIntervalDuration
    field_simp [hApos.ne', hLpos.ne']
    ring
  rw [heq]
  norm_num


theorem terminalCommonInterval_eventually_large
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (V : GeneralizedBlowupSequence.{u}) (K eta : ℝ) :
    ∀ᶠ k in atTop,
      64 * (2 * terminalCommonIntervalDuration S B K + 1) ≤ V.scale k ∧
      B.curvature_threshold ≤ V.scale k ∧
      blowupPinchingThreshold (8 * K) eta ≤ V.scale k := by
  filter_upwards [V.scalar_diverges.eventually
      (eventually_ge_atTop (64 * (2 * terminalCommonIntervalDuration S B K + 1))),
    V.scalar_diverges.eventually (eventually_ge_atTop B.curvature_threshold),
    V.scalar_diverges.eventually (eventually_ge_atTop (blowupPinchingThreshold (8 * K) eta))]
    with k htime hlarge hpinch
  exact ⟨htime, hlarge, hpinch⟩



theorem terminalCommonInterval_stopped_curvature
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    {K : ℝ} (hK : 1 ≤ K) (p : SurgeryParameterPrefix S.constants)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    {base Q r a eta : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hScale : 64 * (2 * terminalCommonIntervalDuration S B K + 1) ≤ Q)
    (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
    (hPinched : SurgeryFlowPinched F)
    (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    (P : M46Predecessors.{u}) {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier}
    (e : SurgeryFlowCylinder F Z base Q (Icc a 0) U)
    (ha : a ∈ Icc (-2 * terminalCommonIntervalDuration S B K) 0)
    (hTerminal : ∀ x ∈ U, (F.connection (base + 0 / Q)).scalarCurvature
      (e.forward 0 ⟨ha.2, le_rfl⟩ x) ≤ (2 * K) * Q)
    (heta : 0 < eta) (hPinchingScale : blowupPinchingThreshold (8 * K) eta ≤ Q) :
    ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
      (F.connection (base + s / Q)).scalarCurvature (e.forward s hs x) ≤ (8 * K) * Q ∧
      |(F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs x)| ≤
        (13 * max (8 * K) 1) * Q ∧
      (F.connection (base + s / Q)).negativeCurvaturePart (e.forward s hs x) ≤ eta * Q := by
  have hd := terminalCommonInterval_duration_bounds S B hK
  have hdelta := hd.1
  have hA := blowupAnalyticConstant_pos S B
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hT : 0 ≤ 2 * terminalCommonIntervalDuration S B K := by positivity
  have haT : -(2 * terminalCommonIntervalDuration S B K) ≤ a := by linarith [ha.1]
  have hL : 1 ≤ 2 * K := by linarith
  have hshort : 64 * blowupAnalyticConstant S B * (2 * K) * (-a) ≤ 1 := by
    apply le_trans _ hd.2.2
    apply mul_le_mul_of_nonneg_left (by linarith [ha.1])
    positivity
  have hpinch : blowupPinchingThreshold (4 * (2 * K)) eta ≤ Q := by
    simpa only [show 4 * (2 * K) = 8 * K by ring] using hPinchingScale
  intro s hs x hx
  have hscalar := first_failure_search_scalar_bound S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
    ⟨P.m04, P.m13.ordinary_flow⟩ e ha.2 haT hx hL (hTerminal x hx) hshort s hs
  have hcurv := first_failure_search_curvature_bounds S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap
    P e ha.2 haT hx hL (hTerminal x hx) hshort heta hpinch s hs
  exact ⟨by nlinarith only [hscalar], by
    simpa only [show 4 * (2 * K) = 8 * K by ring] using hcurv⟩

end PoincareConjecture.M47
