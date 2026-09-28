import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalBirthBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalSurvival
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_InitialSphereControl
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderCutoff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance initialSurvivalCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialSurvivalCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance initialSurvivalTwoJetNorm : NormedAddCommGroup
    (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance initialSurvivalTwoJetSpace : NormedSpace ℝ
    (MetricTwoJet 3) := Prod.normedSpace






theorem exists_initial_outer_survival_cutoff
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    (constants : MetricSurgeryConstants) {epsilon C r A : ℝ}
    (hepsilon : 0 < epsilon) (hC : 0 < C) (hr : 0 < r) (hA : 0 < A) :
    ∃ R0 tau : ℝ, A < R0 ∧ 2 < R0 ∧ 0 < tau ∧
      ∀ R : ℝ, R0 ≤ R → ∃ deltaBar : ℝ, 0 < deltaBar ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      F.local_constants = constants → F.parameters.epsilon = epsilon →
      F.parameters.C = C →
      ∀ (O : SurgeryObservation F) (setup : SurgeryControlSetup constants)
        {start rNext : ℝ},
      SurgeryFixedScalesOn setup F O start rNext deltaBar →
      ∀ (a : ℝ) (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier],
      F.parameters.delta a ≤ deltaBar → ∀ i : Fin (F.event a ha).cap_count,
      ∀ B c d : ℝ, 0 < c → d ≤ B →
      (∀ s ∈ Ico 0 B,
        a + s / ((F.parameters.h a)⁻¹ ^ 2) ∈ surgeryObservationInterval O ∩ Ici start) →
      SurgeryCanonicalOn F (surgeryObservationInterval O) r → SurgeryFlowPinched F →
      ∀ outer : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2)
        (Ico 0 c) ((F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R)),
      (∀ hs x, x ∈ (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R) →
        HEq (outer.forward 0 hs x) x) →
      (∀ b : ℝ, c < b → b ≤ B →
        ¬ ∃ e' : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2)
          (Ico 0 b) ((F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R)),
          ∀ hs x, x ∈ (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R) →
            HEq (e'.forward 0 hs x) x) →
      ∀ {V : Set (F.slice a).carrier},
      V ⊆ (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R) →
      V.Nonempty →
      ∀ inner : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2) (Ico 0 d) V,
      (∀ hs x, x ∈ V → HEq (inner.forward 0 hs x) x) → min d tau ≤ c := by
  obtain ⟨x, u, v, _hcompact, hcollar⟩ :=
    exists_global_standard_collar standard hC (theta := 0) le_rfl zero_lt_one
  have hJ := hcollar 0 ⟨le_rfl, le_rfl⟩
  change metricTwoJet (standard.flow.base.flow.metric 0).euclideanCoefficients x ∈
    collarJetRegion C u v at hJ
  rw [standard.flow.base.initial_metric] at hJ
  obtain ⟨length, center, N, accuracy, haccuracy, hmargin⟩ :=
    exists_standard_sphere_margin standard (theta := 0) le_rfl zero_lt_one
  let sphereSet := range (StandardCylinderPatch.sphereMap N)
  have hsphereCompact : IsCompact sphereSet :=
    isCompact_range (StandardCylinderPatch.sphereMap N).continuous
  obtain ⟨S, _hS, hAS, hsub⟩ := exists_standard_ball_containing_compact g0
    (hsphereCompact.union (isCompact_singleton (x := x))) A
  let R0 := S + 3
  have hR0 : 2 < R0 := by
    have hS : 0 < S := hA.trans hAS
    dsimp [R0]
    linarith only [hS]
  have hAR0 : A < R0 := by dsimp [R0]; linarith
  have hinside : sphereSet ∪ {x} ⊆ g0.metric.ball 0 (R0 - 2) := by
    intro y hy
    exact (hsub hy).trans_le (ENNReal.ofReal_le_ofReal (by dsimp [R0]; linarith))
  have hx : x ∈ g0.metric.ball 0 (R0 - 2) := hinside (Or.inr (mem_singleton x))
  have hsphereInside : sphereSet ⊆ g0.metric.ball 0 (R0 - 2) :=
    fun _ hy => hinside (Or.inl hy)
  obtain ⟨d0, tau0, M, hd0, htau0, hM, hbound⟩ :=
    exists_initial_cylinder_bound P g0 standard.initial_estimate C x u v hJ hR0 hx
  let K := 13 * max (2 * M) (Real.exp 4)
  have hK : 0 < K :=
    mul_pos (by norm_num) ((by linarith : 0 < 2 * M).trans_le (le_max_left _ _))
  obtain ⟨d1, tau1, hd1, htau1, htwo⟩ :=
    exists_initial_cylinder_twoJet_control P g0 hsphereCompact hR0 hsphereInside
      (H := 1) zero_lt_one hK haccuracy
  obtain ⟨dh, hdh, hheight⟩ := exists_surgery_normalization_cutoff hepsilon hr
  let tau := min 1 (min tau0 tau1)
  have htau : 0 < tau := lt_min zero_lt_one (lt_min htau0 htau1)
  have htauOne : tau ≤ 1 := min_le_left _ _
  have htau0' : tau ≤ tau0 := (min_le_right _ _).trans (min_le_left _ _)
  have htau1' : tau ≤ tau1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R0, tau, hAR0, hR0, htau, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  let compactBall := {y : E | g0.metric.edist 0 y ≤ ENNReal.ofReal R}
  have hcompactBall : IsCompact compactBall := M36.standard_closed_ball_compact g0 hRpos.le
  obtain ⟨d2, alpha, Z, hd2, _halpha, hZ, hcoeff⟩ :=
    exists_initial_comparison_metric_bounds.{u} g0 hcompactBall 0
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  let eta := min (min d0 (min d1 d2) / 2) (1 / (2 * (R + 1)))
  have heta : 0 < eta := lt_min (half_pos (lt_min hd0 (lt_min hd1 hd2))) (by positivity)
  have hetaAll : eta ≤ min d0 (min d1 d2) :=
    (min_le_left _ _).trans (half_le_self (le_of_lt (lt_min hd0 (lt_min hd1 hd2))))
  have heta0 : eta ≤ d0 := hetaAll.trans (min_le_left _ _)
  have heta1 : eta ≤ d1 := hetaAll.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heta2 : eta ≤ d2 := hetaAll.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfit : R < eta⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ heta]
    have hle : eta * (2 * (R + 1)) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * (R + 1))).mp (min_le_right _ _)
    nlinarith
  obtain ⟨dc, hdc, hcomparison⟩ :=
    exists_initial_cap_exact_comparison_cutoff.{u} g0 constants heta
  have hk : (0 : ℝ) < 1 / 4 := by norm_num
  let dr := cylinderRemovalCutoff.{u} g0 (H := 1) hRpos hK hZpos hk
  have hdr : 0 < dr := cylinderRemovalCutoff_pos.{u} g0 (H := 1) hRpos hK hZpos hk
  refine ⟨min dc (min dh dr), lt_min hdc (lt_min hdh hdr), ?_⟩
  intro F hg0 hconstants heps hconstant O setup start rNext hscales
    a ha _ hdelta i B c d hc hdB hclock hcanonical hpinch outer hinitial hstop
    V hVU hV inner hinitialInner
  by_contra hnot
  have hclim : c < min d tau := lt_of_not_ge hnot
  have hcd : c < d := hclim.trans_le (min_le_left _ _)
  have hctau : c < tau := hclim.trans_le (min_le_right _ _)
  have hcB : c < B := hcd.trans_le hdB
  have hcOne : c ≤ 1 := hctau.le.trans htauOne
  have ha0 := F.time_domain_nonnegative (F.surgery_times_subset ha)
  have hh := F.parameters.h_pos a ha0
  obtain ⟨hsmall, hthreshold⟩ := hheight F.parameters heps a ha0
    (hdelta.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hq : F.parameters.h a ^ 2 * (r⁻¹ ^ 2) ≤ 1 := by
    simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hthreshold
  obtain ⟨Q, _hlink, hballs⟩ := hcomparison F hg0 hconstants a ha
    (hdelta.trans (min_le_left _ _)) i
  have hcanonical' (s : ℝ) (hs : s ∈ Ico (0 : ℝ) c)
      (y : (F.slice (a + s / ((F.parameters.h a)⁻¹ ^ 2))).carrier)
      (hy : r⁻¹ ^ 2 ≤ (F.connection (a + s / ((F.parameters.h a)⁻¹ ^ 2))).scalarCurvature y) :
      SurgeryCanonicalControl F (a + s / ((F.parameters.h a)⁻¹ ^ 2)) y
        F.parameters.epsilon C := by
    rw [← hconstant]
    exact hcanonical _ (hclock s ⟨hs.1, hs.2.trans hcB⟩).1
      (outer.time_subset (mem_image_of_mem _ hs)) y hy
  obtain ⟨f, hfsource, hftarget, hfmap, G, p, hcontrolled⟩ :=
    hbound F hg0 a ha i hR hfit hc hsmall hq Q heta0 hballs outer hinitial
      hcanonical' hpinch
  have hcurv (s : ℝ) (hs : s ∈ Ico (0 : ℝ) c) (y) :
      (G.flow.connection s).curvatureTensorNorm y ≤ K := by
    let T := (s + c) / 2
    have hT : 0 < T := by dsimp [T]; linarith only [hs.1, hc]
    have hTc : T < c := by dsimp [T]; linarith only [hs.2]
    have hsT : s ≤ T := by dsimp [T]; linarith only [hs.2]
    exact (hcontrolled T hT hTc (hTc.le.trans (hctau.le.trans htau0'))).2
      s ⟨hs.1, hsT⟩ y |>.2
  subst g0
  have hfQ : f.source ⊆ F.standard_initial.metric.ball 0 eta⁻¹ := by
    rw [hfsource]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal hfit.le)
  have hbirth : ∀ y ∈ f.source,
      ‖(G.flow.metric 0).pullbackCoefficients (targetChart f p) y‖ ≤ Z := by
    apply cylinder_birth_coefficient_bound F a ha i hc Q outer hinitial f
      (le_of_eq hftarget) hfQ hfmap G p
    intro y hy
    have hyR : y ∈ F.standard_initial.metric.ball 0 R := hfsource ▸ hy
    have hyK : y ∈ compactBall := by
      change F.standard_initial.metric.edist 0 y ≤ ENNReal.ofReal R
      exact le_of_lt hyR
    simpa only [norm_iteratedFDeriv_zero] using
      ((hcoeff _ _ _ _ _ Q heta2).2 y hyK).2 0 le_rfl
  have hball (z : UnitTwoSphere) :
      StandardCylinderPatch.sphereMap N z ∈ F.standard_initial.metric.ball 0 R :=
    (hsphereInside (mem_range_self z)).trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hmargin0 (z : UnitTwoSphere) (J : MetricTwoJet 3)
      (hJ : ‖J - metricTwoJet F.standard_initial.metric.euclideanCoefficients
        (StandardCylinderPatch.sphereMap N z)‖ ≤ accuracy) :
      (z, J) ∈ sphereSectionalJetRegion (StandardCylinderPatch.sphereMap N) (1 / 4) := by
    apply hmargin 0 ⟨le_rfl, le_rfl⟩ z J
    simpa only [MaximalStandardCapFlow.metric, standard.flow.base.initial_metric] using hJ
  have hnear (s : ℝ) (hs : s ∈ Ico (0 : ℝ) c) (_hs0 : (0 : ℝ) ≤ s)
      (z : UnitTwoSphere) :
      ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p))
        (StandardCylinderPatch.sphereMap N z) -
        metricTwoJet F.standard_initial.metric.euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ ≤ accuracy := by
    let T := (s + c) / 2
    have hT : 0 < T := by dsimp [T]; linarith only [hs.1, hc]
    have hTc : T < c := by dsimp [T]; linarith only [hs.2]
    have hsT : s ≤ T := by dsimp [T]; linarith only [hs.2]
    apply htwo F rfl a ha i hR hfit hc Q heta1 hballs f hfsource hfmap outer
      (le_of_eq hftarget) hinitial G p T hT hTc (hTc.le.trans hcOne)
      (hTc.le.trans (hctau.le.trans htau1')) _ s ⟨hs.1, hsT⟩ _ (mem_range_self z)
    intro t ht y
    exact hcurv t ⟨ht.1, ht.2.trans_lt hTc⟩ y
  have hremove := (maximal_cylinder_removal_of_bounds P hRpos hK hZpos hk hpinch O setup
    hscales ((min_le_right dc (min dh dr)).trans (min_le_right dh dr)) hh
    outer hc hcB hcOne hclock hinitial hstop f hfsource hftarget G p hcurv hbirth
    N hball (fun z => metricTwoJet F.standard_initial.metric.euclideanCoefficients
      (StandardCylinderPatch.sphereMap N z)) hc hmargin0 hnear).2
  exact not_disappears_of_surviving_subcylinder outer inner hc hcd hVU hV hinitialInner hremove

end PoincareConjecture.M44
