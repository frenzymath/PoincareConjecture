import PoincareConjecture.Proofs.M47.BlowupControlsSourceScalar
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

private theorem scalar_eq_of_heq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y := by
  cases hst
  cases hxy
  rfl

theorem exists_first_failure_short_search_scalar_bound
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) {A : ℝ} (hA : 0 ≤ A) :
    ∃ Q0 tau K : ℝ, 0 < Q0 ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < K ∧
      ∀ (p : SurgeryParameterPrefix S.constants)
        (_P : M44CapPersistencePredecessors.{u})
        (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      F.standard_initial = S.setup.standard_initial → F.local_constants = S.constants →
      F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
      ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
        {base Q r a : ℝ} (ht : base ∈ H.generalized.interval),
      base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → r⁻¹ ^ 2 ≤ Q →
      SurgeryFlowPinched F →
      SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r →
      (∀ t ∈ surgeryObservationInterval O ∩ Ico (surgeryEpochStart (p.i - 1)) O.H,
        F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants) →
      a ∈ Ico (-tau) 0 → ∀ x : (H.generalized.slice base).carrier,
      H.generalized.scalar ⟨base, x⟩ = Q →
      ∀ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
        ((F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)),
      (∀ hs y,
        y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
          HEq (e.forward 0 hs y) y) →
      ∀ s (hs : s ∈ Icc a 0),
        ∀ y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q),
          (F.connection (base + s / Q)).scalarCurvature (e.forward s hs y) ≤ K * Q := by
  have heSmall : S.setup.epsilon ≤ S.calibration.epsilon₁₀ := by
    linarith [S.calibration.two_epsilon_le_bounded_distance, S.setup.epsilon_pos]
  obtain ⟨D0, D, hD0, hD, hterminal⟩ :=
    exists_search_terminal_scalar_bound S S.setup.epsilon_pos heSmall S.setup.C_pos hA
  let L := max 1 D
  let A0 := blowupAnalyticConstant S B
  let tau := (64 * A0 * L)⁻¹
  let Q0 := max D0 (max 128 B.curvature_threshold)
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hA0 : 1 ≤ A0 := le_max_left _ _
  have hA0pos : 0 < A0 := blowupAnalyticConstant_pos S B
  have hcoefficient : 0 < 64 * A0 * L := by positivity
  have htau : 0 < tau := inv_pos.mpr hcoefficient
  have htauOne : tau ≤ 1 := by
    apply (inv_le_one₀ hcoefficient).mpr
    nlinarith only [hA0, hL, mul_le_mul hA0 hL zero_le_one (by linarith only [hA0])]
  have hQ0 : 0 < Q0 := hD0.trans_le (le_max_left _ _)
  refine ⟨Q0, tau, 4 * L, hQ0, htau, htauOne, by positivity, ?_⟩
  intro p P F O hInitial hConstants he hC W H base Q r a ht hBase hLarge hThreshold
    hPinched hEarlier hOverlap ha x hscale e hbased s hs y hy
  have hQ : 0 < Q := hQ0.trans_le hLarge
  have hD0Q : D0 ≤ Q := (le_max_left _ _).trans hLarge
  have h128 : 128 ≤ Q := (le_max_left 128 B.curvature_threshold).trans
    ((le_max_right D0 _).trans hLarge)
  have hBQ : B.curvature_threshold ≤ Q := (le_max_right 128 B.curvature_threshold).trans
    ((le_max_right D0 _).trans hLarge)
  have hbasepos : 0 < base :=
    (show 0 < surgeryEpochStart p.i by unfold surgeryEpochStart; positivity).trans_le hBase.1
  have hpast : SurgeryCanonicalOn F (Ico 0 base) r := by
    intro t ht' htime z hz
    exact hEarlier t ⟨⟨ht'.1, ht'.2.trans hBase.2⟩, ht'.2⟩ htime z hz
  have hyTerminal := hterminal F W H ht hbasepos hQ ha.2 he hC hPinched hpast
    hThreshold x hscale hD0Q e hbased y hy
  have hread : (F.connection (base + 0 / Q)).scalarCurvature
      (e.forward 0 ⟨ha.2.le, le_rfl⟩ y) = (F.connection base).scalarCurvature y := by
    exact scalar_eq_of_heq (by simp) (hbased _ y hy)
  have hshort : 64 * A0 * L * (-a) ≤ 1 := by
    calc
      _ ≤ (64 * A0 * L) * tau :=
        mul_le_mul_of_nonneg_left (by linarith only [ha.1]) hcoefficient.le
      _ = 1 := mul_inv_cancel₀ hcoefficient.ne'
  have haOne : -(1 : ℝ) ≤ a := by linarith only [ha.1, htauOne]
  have hline := first_failure_search_scalar_bound S B p O hInitial hConstants hC
    hBase (by norm_num : (0 : ℝ) ≤ 1) (by norm_num; exact h128) hBQ hThreshold
    hPinched hEarlier hOverlap P e ha.2.le haOne hy hL
    (hread.trans_le (hyTerminal.trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 D) hQ.le))) hshort s hs
  exact hline

end PoincareConjecture.M47
