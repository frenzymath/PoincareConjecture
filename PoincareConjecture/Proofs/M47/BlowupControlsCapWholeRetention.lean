import PoincareConjecture.Proofs.M47.BlowupControlsCapTerminalBounds
import PoincareConjecture.Proofs.M47.BlowupControlsCapCurvature
import PoincareConjecture.Proofs.M47.BlowupControlsCapBirthMetric
import PoincareConjecture.Proofs.M47.BlowupControlsCapSphere











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

noncomputable local instance wholeCapCoefficientNorm : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance wholeCapCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance wholeCapTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance wholeCapTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace



theorem exists_actualCap_whole_retention_cutoff
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta : theta < 1) (A0 : ℝ) :
    ∃ A eta0 delta0 : ℝ, 0 < A ∧ A0 < A ∧ 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow → SurgeryFlowPinched F →
      ∀ (O : SurgeryObservation F) {constants : MetricSurgeryConstants}
        (setup : SurgeryControlSetup constants) {start rNext deltaBar : ℝ},
      SurgeryFixedScalesOn setup F O start rNext deltaBar → deltaBar ≤ delta0 →
      ∀ (t : ℝ) (hbirth : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hbirth).cap_count) (c : ℝ), 0 < c → c ≤ theta →
      ∀ (U V : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) (Ico 0 c) U)
        (survivor : SurgeryFlowCylinder F (F.slice t) t
          ((F.parameters.h t)⁻¹ ^ 2) (Icc 0 c) V)
        (initial : SurgeryCapInitialComparison F t hbirth i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart → (F.parameters.h t) ^ 2 ≤ 1 →
      ∀ (hT : t + c / ((F.parameters.h t)⁻¹ ^ 2) ∈ F.surgery_times)
        (_hnTop : Nonempty (F.slice (t + c / ((F.parameters.h t)⁻¹ ^ 2))).carrier),
      t + c / ((F.parameters.h t)⁻¹ ^ 2) ∈ surgeryObservationInterval O ∩ Ici start →
      ∀ (r : ℝ) (hr : r ∈ Ico 0 c)
        (hr' : t + r / ((F.parameters.h t)⁻¹ ^ 2) ∈
          Ico (F.event (t + c / ((F.parameters.h t)⁻¹ ^ 2)) hT).tMinus
            (t + c / ((F.parameters.h t)⁻¹ ^ 2))),
      (∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x) →
      (∀ hs x, x ∈ V → HEq (survivor.forward 0 hs x) x) →
      ∀ y : (F.slice t).carrier, y ∈ U → y ∈ V →
      ∀ x ∈ U, ((F.event (t + c / ((F.parameters.h t)⁻¹ ^ 2)) hT).pre_identify
        ⟨t + r / ((F.parameters.h t)⁻¹ ^ 2), hr'⟩).symm (e.forward r hr x) ∈
          interior (F.event (t + c / ((F.parameters.h t)⁻¹ ^ 2)) hT).retained_pre := by
  obtain ⟨K0, hK0, hscalarChoice⟩ := exists_actualCap_scalar_upper.{u} standard htheta0 htheta
  obtain ⟨A, hA, hA0, length, center, N, tolerance, htolerance, hball, hmargin⟩ :=
    exists_cap_sphere_buffer standard htheta0 htheta A0
  obtain ⟨etaS, hetaS, _hetaSHalf, hscalar⟩ := hscalarChoice A hA
  obtain ⟨Z, etaB, hZ, hetaB, _hetaBHalf, hbirthMetric⟩ :=
    exists_actualCap_birth_metric_bound.{u} standard htheta0 htheta hA
  obtain ⟨etaN, hetaN, _hetaNHalf, hsphere⟩ :=
    exists_actualCap_sphere_twoJet_tail.{u} standard htheta hA N hball htolerance
  let K1 : ℝ := 13 * max K0 (Real.exp 4)
  have hK1 : 0 < K1 := mul_pos (by norm_num)
    ((Real.exp_pos 4).trans_le (le_max_right _ _))
  have hk : (0 : ℝ) < 1 / 4 := by norm_num
  let delta0 := M44.laterNeckRemovalCutoff.{u} hK0
    (M44.cylinderRemovalDiameter_pos g0 (K := K1) (H := theta) hA hZ) hk
  let eta0 := min (1 / 2) (min etaS (min etaB etaN))
  have heta0 : 0 < eta0 := lt_min (by norm_num) (lt_min hetaS (lt_min hetaB hetaN))
  refine ⟨A, eta0, delta0, hA, hA0, heta0, min_le_left _ _,
    M44.laterNeckRemovalCutoff_pos.{u} _ _ _, ?_⟩
  intro F hinitial S hS hpinch O constants setup start rNext deltaBar hscales hdelta
    t hbirth hn i c hc hctheta U V e survivor initial eta heta hetaSmall comparison hsmall
    hT hnTop htime r hr hr' based basedSurvivor y hyU hyV
  have hetaS' : eta ≤ etaS :=
    hetaSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaB' : eta ≤ etaB :=
    hetaSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hetaN' : eta ≤ etaN :=
    hetaSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let q := capInitialPartialDiffeomorph initial
  have htarget : q.target = U := comparison.choose_spec.2.2.2.1
  have hsource : q.source = g0.metric.ball 0 A := by
    change F.standard_initial.metric.ball 0 A = g0.metric.ball 0 A
    rw [hinitial]
  have hU : IsOpen U := htarget ▸ q.open_target
  have hh := F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hbirth))
  obtain ⟨G⟩ := M44.exists_cylinderRicciFlow P hpinch e hU hc q (le_of_eq htarget)
  let p : (⟨q.target, q.open_target⟩ : Opens (F.slice t).carrier) :=
    ⟨y, htarget.symm ▸ hyU⟩
  have hscalarAll (s : ℝ) (hs : s ∈ Ico 0 c) (x) (hx : x ∈ U) :
      (F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward s hs x) ≤ K0 :=
    hscalar F hinitial S hS t hbirth hn i (Ico 0 c) U e initial eta heta hetaS' comparison
      hh s hs (hs.2.le.trans hctheta) x hx
  have hcurv := cap_normalized_curvature_bound P hpinch e hU q (le_of_eq htarget) G
    hsmall hscalarAll
  have hbirthAll (x : StandardCapSpace) (hx : x ∈ q.source) :
      ‖(G.flow.metric 0).pullbackCoefficients (M44.targetChart q p) x‖ ≤ Z :=
    hbirthMetric F hinitial S hS t hbirth hn i (Ico 0 c) U e initial eta heta hetaB'
      comparison G p ⟨le_rfl, hc⟩ x hx
  obtain ⟨s0, hs0, hnear⟩ := hsphere F hinitial S hS t hbirth hn i c hc hctheta U e
    initial eta heta hetaN' comparison G p
  have hmargin' : ∀ z J', ‖J' - metricTwoJet (S.metric c).euclideanCoefficients
      (M44.StandardCylinderPatch.sphereMap N z)‖ ≤ tolerance →
      (z, J') ∈ M44.sphereSectionalJetRegion
        (M44.StandardCylinderPatch.sphereMap N) (1 / 4) := by
    cases hinitial
    cases hS
    exact hmargin c ⟨hc.le, hctheta⟩
  exact cap_preterminal_retained_of_comparison_estimates P hA hK0 hK1.le hZ hk hpinch
    O setup hscales hdelta hh e survivor hc hctheta q hsource htarget G p hscalarAll hcurv
    hbirthAll N hball (fun z => metricTwoJet (S.metric c).euclideanCoefficients
      (M44.StandardCylinderPatch.sphereMap N z)) hs0 hmargin' hnear hT htime r hr hr'
    based basedSurvivor y hyU hyV

end PoincareConjecture.M47
