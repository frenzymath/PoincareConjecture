import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapAlternative
import PoincareConjecture.Proofs.M47.CanonicalStandardRecutCover
import PoincareConjecture.Proofs.M47.CanonicalStandardCapCarrier










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47



theorem standard_cap_alternative_setup_recut
    (S : RepairedControlledSchedulesData.{u}) {v : ℝ}
    (hv : v ∈ Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime)
    {z : StandardCapSpace}
    (N : StandardCapNeighborhood S.cap_persistence.standard_cap.atlas
      S.cap_persistence.standard_cap.flow v
      (S.calibration.beta * S.setup.epsilon / 3) S.calibration.Cstandard z) :
    ∃ H : CapCertificate (S.cap_persistence.standard_cap.flow.metric v),
      H.epsilon = S.setup.epsilon ∧ H.cap_constant ≤ S.setup.C ∧
      H.connection = S.cap_persistence.standard_cap.flow.connection v ∧ z ∈ H.core := by
  obtain ⟨refined⟩ := S.calibration.cap_refinement v z N
  have he := S.setup.epsilon_pos
  have hsmall : S.setup.epsilon ≤ 1 / 200 :=
    S.setup.epsilon_le.trans (min_le_left _ _)
  have hbeta := S.calibration.beta_lt_half
  have hgamma : refined.cap.epsilon ≤ 1 / 1200 := by
    rw [refined.epsilon_eq]
    have h := mul_le_mul hbeta.le hsmall he.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [h]
  have haccuracy : 6 * refined.cap.epsilon ≤ S.setup.epsilon := by
    rw [refined.epsilon_eq]
    have h := mul_le_mul_of_nonneg_right hbeta.le he.le
    nlinarith only [h]
  obtain ⟨H, hHe, hHC, _hcarrier, hHD, hcore⟩ :=
    Proofs.M47.exists_same_constant_epsilon_recut refined.cap
      (Proofs.M47.standard_metric_complete S.cap_persistence.standard_cap hv)
      hgamma he hsmall haccuracy
  refine ⟨H, hHe, ?_, hHD.trans refined.connection_eq, hcore refined.contains⟩
  rw [hHC, refined.constant_eq, S.calibration.setup_C_eq]
  exact le_max_right _ _




theorem exists_source_standard_cap_canonical_neighborhood
    (S : RepairedControlledSchedulesData.{u}) {theta v : ℝ}
    (htheta : theta < 1) (hv : v ∈ Icc 0 theta) {z : StandardCapSpace}
    (N : StandardCapNeighborhood S.cap_persistence.standard_cap.atlas
      S.cap_persistence.standard_cap.flow v
      (S.calibration.beta * S.setup.epsilon / 3) S.calibration.Cstandard z) :
    ∃ A0 eta0 delta : ℝ, ∃ V : Set StandardCapSpace,
      0 < A0 ∧ 0 < eta0 ∧ 0 < delta ∧ IsOpen V ∧ z ∈ V ∧
      ∀ A : ℝ, A0 ≤ A →
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = S.standard_initial →
      ∀ model : MaximalStandardCapFlow F.standard_initial,
        HEq model S.cap_persistence.standard_cap.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (_comparison : SurgeryCapFamilyComparison F model A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
        s ≤ theta → |s - v| < delta → ∀ z' ∈ V,
          SurgeryCanonicalControl F (t + s / ((F.parameters.h t)⁻¹ ^ 2))
            (e.forward s hs (initial.chart z')) S.setup.epsilon S.setup.C := by
  have hvtime : v ∈ Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime := by
    rw [S.cap_persistence.standard_cap.lifetime_one]
    exact ⟨hv.1, hv.2.trans_lt htheta⟩
  obtain ⟨H, hHe, hHC, hHD, hz⟩ := standard_cap_alternative_setup_recut S hvtime N
  let R := (S.standard_initial.metric.edist 0 z).toReal + 1
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hzR : S.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal R := by
    calc
      _ = ENNReal.ofReal (S.standard_initial.metric.edist 0 z).toReal :=
        (ENNReal.ofReal_toReal (S.standard_initial.metric.edist_ne_top 0 z)).symm
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by dsimp only [R]; linarith)
  obtain ⟨A0, hA0, _hRA, hbuffer⟩ :=
    Proofs.M47.exists_standard_cap_uniform_initial_ball S.cap_persistence
      (hv.1.trans hv.2) htheta S.setup.C_pos hR
  have hsource : H.carrier ⊆ S.standard_initial.metric.ball 0 A0 :=
    subset_closure.trans (hbuffer v hv H hHD hHC z hz hzR).2
  obtain ⟨eta0, delta, heta0, hdelta, transfer⟩ :=
    Proofs.M47.exists_actualCap_nearby_physical_certificate_tolerance
      S.cap_persistence.standard_cap htheta hA0 hv H hHD hsource
  have hcoreOpen : IsOpen H.core := by
    rw [H.core_eq_interior_closed_core]
    exact isOpen_interior
  refine ⟨A0, eta0, delta, H.core, hA0, heta0, hdelta, hcoreOpen, hz, ?_⟩
  intro A hA F hInitial model hmodel t hT hn i J U e initial eta heta hetaSmall
    comparison hh s hs hst hnear z' hz'
  obtain ⟨small, _esmall, _comparisonSmall, hchart, _hinverse⟩ :=
    restrict_cap_family_comparison i e initial comparison hA0 hA
  have hball : F.standard_initial.metric.ball 0 A0 ⊆
      F.standard_initial.metric.ball 0 A := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hA)
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A0 ⊆ U := by
    rw [← comparison.choose_spec.2.2.2.1]
    exact image_mono hball
  let esmall := e.restrict Subset.rfl e.interval_connected himage
  have comparisonSmall : SurgeryCapFamilyComparison F model A0 eta esmall small.chart := by
    obtain ⟨bound, hbound, hlifetime, hinterval, _himage, hjets⟩ := comparison
    refine ⟨bound, hbound, hlifetime, hinterval, ?_, ?_⟩
    · rw [hchart]
    · intro u hu x hx
      rw [hchart]
      exact hjets u hu x (hball hx)
  obtain ⟨target, hTe, hTC, hTD, hTcore, _hTcarrier⟩ :=
    transfer F hInitial model hmodel t hT hn i J
      (initial.chart '' F.standard_initial.metric.ball 0 A0)
      esmall small eta heta hetaSmall comparisonSmall hh s hs hst hnear
  have hpoint : actualCapSliceChart esmall small comparisonSmall s hs z' ∈ target.core := by
    rw [hTcore]
    exact mem_image_of_mem _ hz'
  have hpoint' : e.forward s hs (initial.chart z') ∈ target.core := by
    simpa only [actualCapSliceChart_apply, hchart, esmall,
      SurgeryFlowCylinder.restrict_forward] using hpoint
  exact SurgeryCanonicalControl.cap target (hTe.trans hHe) (hTC.trans_le hHC) hTD hpoint'

end PoincareConjecture.M47
