import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapStop
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthFactory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46

structure SourceSearchCapBirthComparison
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) (t : ℝ)
    (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier]
    (i : Fin (F.event t hT).cap_count) (A eta : ℝ) where
  I : Set ℝ
  e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I
    ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t))
  initial : SurgeryCapInitialComparison F t hT i A
  comparison : SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart
  based : ∀ hs z,
    z ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) →
      HEq (e.forward 0 hs z) z

theorem source_search_cap_birth_comparison_of_positive_age
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {C : GeneralizedSliceCarrier.{u}} {origin scale a : ℝ}
    {U : Set C.carrier} (E : SurgeryFlowCylinder F C origin scale (Icc a 0) U)
    (ha : a < 0)
    (hbirthH : origin + a / scale < O.H)
    {A eta theta : ℝ}
    (hT : origin + a / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + a / scale)).carrier]
    (i : Fin (F.event (origin + a / scale) hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (hpersist : SurgeryCapPersistenceAlternative F O (origin + a / scale)
      hT i A eta theta)
    (hmargin : (O.H - (origin + a / scale)) /
      (F.parameters.h (origin + a / scale)) ^ 2 < theta)
    {V : Set (F.slice (origin + a / scale)).carrier}
    (f : SurgeryFlowCylinder F (F.slice (origin + a / scale))
      (origin + a / scale) ((F.parameters.h (origin + a / scale))⁻¹ ^ 2)
      (Icc 0 ((O.H - (origin + a / scale)) /
        (F.parameters.h (origin + a / scale)) ^ 2)) V)
    (hfbased : ∀ hs y, y ∈ V → HEq (f.forward 0 hs y) y)
    (x : C.carrier)
    (hyV : E.forward a ⟨le_rfl, ha.le⟩ x ∈ V)
    (hycap : E.forward a ⟨le_rfl, ha.le⟩ x ∈
      ((F.event (origin + a / scale) hT).caps i).carrier) :
    let birth := origin + a / scale
    let h := F.parameters.h birth
    let d := (O.H - birth) / h ^ 2
    0 < d ∧ d < theta ∧
      ∃ comparison : SourceSearchCapBirthComparison F O birth hT i A eta,
        comparison.I = Ico 0 d := by
  let birth : ℝ := origin + a / scale
  let h : ℝ := F.parameters.h birth
  let d : ℝ := (O.H - birth) / h ^ 2
  have hbirth : birth < O.H := by
    simpa only [birth] using hbirthH
  have hh : 0 < h := by
    dsimp only [h]
    exact F.parameters.h_pos birth
      (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hd : 0 < d := by
    dsimp only [d]
    exact div_pos (sub_pos.mpr hbirth) (sq_pos_of_pos hh)
  have hmargin' : d < theta := by
    simpa only [d, birth, h] using hmargin
  obtain ⟨closed, initial, hcomparison, hclosedBased⟩ :=
    Proofs.M47.capPersistence_persists_to_horizon O hT i hA V f hfbased
      (E.forward a ⟨le_rfl, ha.le⟩ x) hyV hycap hmargin' hpersist
  refine ⟨hd, hmargin', ?_⟩
  refine ⟨{
    I := Ico 0 d
    e := closed
    initial := initial
    comparison := hcomparison
    based := hclosedBased
  }, rfl⟩

theorem exists_zero_age_search_cap_birth_comparison_cutoff
    (S : RepairedControlledSchedulesData.{u}) {Asearch : ℝ} (hAsearch : 0 < Asearch) :
    ∃ Q0 R : ℝ, 0 < Q0 ∧
      S.standard_initial.cylindrical_end.radius + 5 < R ∧
      ∀ A : ℝ, R ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 1000 →
        ∃ delta : ℝ, 0 < delta ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          F.standard_initial = S.standard_initial →
          F.local_constants = S.constants →
          F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
          HEq O.standard_flow S.cap_persistence.standard_cap.flow →
        ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
          {base Q r : ℝ} (ht : base ∈ H.generalized.interval), 0 < base → 0 < Q →
          SurgeryFlowPinched F → SurgeryCanonicalOn F (Ico 0 base) r → r⁻¹ ^ 2 ≤ Q →
        ∀ x : (H.generalized.slice base).carrier,
          H.generalized.scalar ⟨base, x⟩ = Q → Q0 ≤ Q →
        ∀ (hT : base ∈ F.surgery_times), ∀ [Nonempty (F.slice base).carrier],
          F.parameters.delta base ≤ delta →
        ∀ (i : Fin (F.event base hT).cap_count) (y : (F.slice base).carrier),
          y ∈ (F.metric base).ball (H.history.forward base ht x)
              (Asearch / Real.sqrt Q) →
          y ∈ ((F.event base hT).caps i).carrier →
          ∃ j : Fin (F.event base hT).cap_count,
            ∃ comparison : SourceSearchCapBirthComparison F O base hT j A eta,
              comparison.I = Icc 0 0 ∧
              ((F.metric base).ball (H.history.forward base ht x)
                  (Asearch / Real.sqrt Q) ⊆
                (F.metric base).ball ((F.event base hT).caps j).tip
                  (R * F.parameters.h base)) ∧
              ∃ z ∈ F.standard_initial.metric.ball 0 A,
                comparison.initial.chart z = H.history.forward base ht x ∧
                F.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * R) := by
  obtain ⟨Q0, R, hQ0, hR, hcutoff⟩ :=
    exists_zero_age_search_cap_comparison_cutoff S hAsearch
  refine ⟨Q0, R, hQ0, hR, ?_⟩
  intro A hRA eta heta hetaSmall
  obtain ⟨delta, hdelta, hmain⟩ := hcutoff A hRA eta heta hetaSmall
  refine ⟨delta, hdelta, ?_⟩
  intro F O hInitial hConstants hepsilon hC hmodel W H base Q r ht hbase hQ
    hpinch hpast hthreshold x hscale hlarge hT hn hsmall i y hy hycap
  obtain ⟨j, e, initial, comparison, based, hcapture, z, hz, hzp, hzR⟩ :=
    hmain F hInitial hConstants hepsilon hC O.standard_flow hmodel W H ht hbase hQ
      hpinch hpast hthreshold x hscale hlarge hT hsmall i y hy hycap
  refine ⟨j, {
    I := Icc 0 0
    e := e
    initial := initial
    comparison := comparison
    based := based
  }, rfl, hcapture, ?_⟩
  exact ⟨z, hz, hzp, hzR⟩

end PoincareConjecture.M47
