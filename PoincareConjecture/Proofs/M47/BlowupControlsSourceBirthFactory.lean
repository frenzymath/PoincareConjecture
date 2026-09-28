import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthCapture
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthCenter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_zero_age_search_cap_comparison_cutoff
    (S : RepairedControlledSchedulesData.{u}) {Asearch : ℝ} (hAsearch : 0 < Asearch) :
    ∃ Q0 R : ℝ, 0 < Q0 ∧ S.standard_initial.cylindrical_end.radius + 5 < R ∧
      ∀ A : ℝ, R ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 1000 →
        ∃ delta : ℝ, 0 < delta ∧
        ∀ (F : SurgeryFlowData.{u}), F.standard_initial = S.standard_initial →
          F.local_constants = S.constants →
          F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
        ∀ model : MaximalStandardCapFlow F.standard_initial,
          HEq model S.cap_persistence.standard_cap.flow →
        ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W) {base Q r : ℝ}
          (ht : base ∈ H.generalized.interval), 0 < base → 0 < Q →
          SurgeryFlowPinched F → SurgeryCanonicalOn F (Ico 0 base) r → r⁻¹ ^ 2 ≤ Q →
        ∀ x : (H.generalized.slice base).carrier,
          H.generalized.scalar ⟨base, x⟩ = Q → Q0 ≤ Q →
        ∀ (hT : base ∈ F.surgery_times), ∀ [Nonempty (F.slice base).carrier],
          F.parameters.delta base ≤ delta →
        ∀ (i : Fin (F.event base hT).cap_count) (y : (F.slice base).carrier),
          y ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
          y ∈ ((F.event base hT).caps i).carrier →
          ∃ j : Fin (F.event base hT).cap_count,
            ∃ e : SurgeryFlowCylinder F (F.slice base) base ((F.parameters.h base)⁻¹ ^ 2)
                (Icc 0 0)
                ((F.metric base).ball ((F.event base hT).caps j).tip
                  (A * F.parameters.h base)),
              ∃ initial : SurgeryCapInitialComparison F base hT j A,
                SurgeryCapFamilyComparison F model A eta e initial.chart ∧
                (∀ hs w, w ∈ (F.metric base).ball ((F.event base hT).caps j).tip
                  (A * F.parameters.h base) → HEq (e.forward 0 hs w) w) ∧
                ((F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) ⊆
                  (F.metric base).ball ((F.event base hT).caps j).tip
                    (R * F.parameters.h base)) ∧
                ∃ z ∈ F.standard_initial.metric.ball 0 A,
                  initial.chart z = H.history.forward base ht x ∧
                  F.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * R) := by
  obtain ⟨Q0, R, delta0, hQ0, hR, hdelta0, capture⟩ :=
    exists_zero_age_search_cap_capture_cutoff S hAsearch.le
  have hRpos : 0 < R := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  refine ⟨Q0, R, hQ0, hR, ?_⟩
  intro A hRA eta heta hetaSmall
  have hA : 0 < A := hRpos.trans_le hRA
  obtain ⟨delta1, hdelta1, birth⟩ :=
    exists_cap_birth_family_comparison_cutoff S.standard_initial S.constants hA heta
  let delta := min delta0 delta1
  refine ⟨delta, lt_min hdelta0 hdelta1, ?_⟩
  intro F hinitial hconstants hepsilon hC model hmodel W H base Q r ht hbase hQ
    hpinch hpast hthreshold x hscale hlarge hT hn hsmall i y hy hycap
  obtain ⟨j, hcapture⟩ := capture F hinitial hconstants hepsilon hC W H ht hbase hQ
    hpinch hpast hthreshold x hscale hlarge hT
      (hsmall.trans (min_le_left _ _)) i y hy hycap
  have hlifetime : model.base.lifetime = 1 := by
    have hpair : (⟨F.standard_initial, model⟩ :
        Σ g : StandardInitialMetric, MaximalStandardCapFlow g) =
        ⟨S.standard_initial, S.cap_persistence.standard_cap.flow⟩ :=
      Sigma.ext hinitial hmodel
    exact (congrArg (fun p : Σ g : StandardInitialMetric, MaximalStandardCapFlow g =>
      p.2.base.lifetime) hpair).trans S.cap_persistence.standard_cap.lifetime_one
  obtain ⟨e, initial, comparison, based⟩ := birth F hinitial hconstants model hlifetime
    base hT (hsmall.trans (min_le_right _ _)) j
  have hcenter : H.history.forward base ht x ∈
      (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) := by
    change (F.metric base).edist _ _ < ENNReal.ofReal (Asearch / Real.sqrt Q)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hAsearch (Real.sqrt_pos.mpr hQ))
  obtain ⟨z, hz, hzp, hzR⟩ := exists_cap_birth_center_in_fixed_ball hRpos hRA
    heta hetaSmall e initial comparison (show (0 : ℝ) ∈ Icc 0 0 from ⟨le_rfl, le_rfl⟩)
      (based _) (hcapture hcenter)
  exact ⟨j, e, initial, comparison, based, hcapture, z, hz, hzp, hzR⟩

end PoincareConjecture.M47
