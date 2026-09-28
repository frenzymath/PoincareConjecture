import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalSurvival
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_GlobalStandardCollar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_SampleRestart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_MaximalSamples











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance restartSurvivalCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance restartSurvivalCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance restartSurvivalTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance restartSurvivalTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace





theorem exists_restarted_outer_survival_cutoff
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {C r A H M Kpast : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hH : 0 < H) (hH1 : H < 1) (hM : 0 < M) :
    ∃ R0 tau accuracy : ℝ, ∃ compact : Set E,
      A < R0 ∧ 2 < R0 ∧ 0 < tau ∧ 0 < accuracy ∧ IsCompact compact ∧
      compact ⊆ g0.metric.ball 0 (R0 - 2) ∧
      ∀ R : ℝ, R0 ≤ R → ∃ eta0 delta0 : ℝ, 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
        {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
        {start rNext deltaBar : ℝ},
      SurgeryFixedScalesOn setup F O start rNext deltaBar → deltaBar ≤ delta0 →
      ∀ (birth : ℝ) (hbirth : birth ∈ F.surgery_times)
        [Nonempty (F.slice birth).carrier] (i : Fin (F.event birth hbirth).cap_count)
        {B : ℝ}, B ≤ H →
      (∀ s ∈ Ico 0 B,
        birth + s / ((F.parameters.h birth)⁻¹ ^ 2) ∈ surgeryObservationInterval O ∩ Ici start) →
      ∀ D : MaximalCapSample g0 F birth hbirth i B,
      D.radius = R → D.eta ≤ eta0 → F.parameters.h birth ^ 2 ≤ 1 →
      F.parameters.h birth ^ 2 * (r⁻¹ ^ 2) ≤ M → F.parameters.C = C →
      SurgeryCanonicalOn F (surgeryObservationInterval O) r → SurgeryFlowPinched F →
      ∀ a : ℝ, 0 ≤ a → a < D.lifetime →
      (∀ y, (D.ordinary.flow.connection a).scalarCurvature y ≤ M) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ y,
        (D.ordinary.flow.connection s).curvatureTensorNorm y ≤ Kpast) →
      (∀ x ∈ compact,
        ‖metricTwoJet (fun y => D.toCylinderCompactnessSample.coefficients (a, y)) x -
          metricTwoJet (standard.flow.metric a).euclideanCoefficients x‖ ≤ accuracy) →
      ∀ {V : Set (F.slice birth).carrier}, V ⊆ D.region → V.Nonempty →
      ∀ {d : ℝ}, d ≤ B →
      ∀ inner : SurgeryFlowCylinder F (F.slice birth) birth ((F.parameters.h birth)⁻¹ ^ 2)
        (Ico 0 d) V,
      (∀ hs x, x ∈ V → HEq (inner.forward 0 hs x) x) →
        min d (a + tau) ≤ D.lifetime := by
  obtain ⟨x, u, v, hmodel, hcollar⟩ := exists_global_standard_collar standard hC hH.le hH1
  let model := (fun t => metricTwoJet (standard.flow.metric t).euclideanCoefficients x) ''
    Icc (0 : ℝ) H
  have hmargin : model ⊆ collarJetRegion C u v := by
    rintro _ ⟨t, ht, rfl⟩
    exact hcollar t ht
  obtain ⟨length, center, N, sphereTolerance, hsphereTolerance, hsphereMargin⟩ :=
    exists_standard_sphere_margin standard hH.le hH1
  let compact := range (StandardCylinderPatch.sphereMap N) ∪ {x}
  have hcompact : IsCompact compact :=
    (isCompact_range (StandardCylinderPatch.sphereMap N).continuous).union isCompact_singleton
  obtain ⟨S, _hS, hAS, hsub⟩ := exists_standard_ball_containing_compact g0 hcompact A
  let R0 := S + 3
  have hR0 : 2 < R0 := by
    have hS : 0 < S := hA.trans hAS
    dsimp [R0]
    linarith only [hS]
  have hAR0 : A < R0 := by dsimp [R0]; linarith
  have hinside : compact ⊆ g0.metric.ball 0 (R0 - 2) := by
    intro y hy
    exact (hsub hy).trans_le (ENNReal.ofReal_le_ofReal (by dsimp [R0]; linarith))
  have hx : x ∈ g0.metric.ball 0 (R0 - 2) := hinside (Or.inr (mem_singleton x))
  obtain ⟨d1, tau1, hd1, htau1, hrestart⟩ :=
    exists_sample_restart_cutoff P g0 C x u v hmodel hmargin hR0 hx hM hH
      (Kpast := Kpast)
  let K := max Kpast (13 * max (2 * M) (Real.exp 4))
  have hK : 0 < K :=
    (mul_pos (by norm_num : (0 : ℝ) < 13)
      ((by linarith : 0 < 2 * M).trans_le (le_max_left _ _))).trans_le (le_max_right _ _)
  obtain ⟨d2, alpha, Z0, L, hd2, _halpha, _hZ0, hL, hest⟩ :=
    exists_cylinder_coordinate_estimates P g0 2 hR0 hH hK
  let tau := min tau1 (sphereTolerance / (2 * (L + 1)))
  let accuracy := min d1 (sphereTolerance / 2)
  have hden : 0 < 2 * (L + 1) := by positivity
  have htau : 0 < tau := lt_min htau1 (div_pos hsphereTolerance hden)
  have haccuracy : 0 < accuracy := lt_min hd1 (half_pos hsphereTolerance)
  refine ⟨R0, tau, accuracy, compact, hAR0, hR0, htau, haccuracy, hcompact, hinside, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  let closedBall := {y : E | g0.metric.edist 0 y ≤ ENNReal.ofReal R}
  have hclosed : IsCompact closedBall := M36.standard_closed_ball_compact g0 hRpos.le
  obtain ⟨d3, alpha3, Z, hd3, _halpha3, hZ, hcoeff⟩ :=
    exists_initial_comparison_metric_bounds.{u} g0 hclosed 0
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hk : (0 : ℝ) < 1 / 4 := by norm_num
  refine ⟨min d1 (min d2 d3), cylinderRemovalCutoff.{u} g0 (H := H) hRpos hK hZpos hk,
    lt_min hd1 (lt_min hd2 hd3), cylinderRemovalCutoff_pos.{u} g0 (H := H) hRpos hK hZpos hk,
    ?_⟩
  intro F O constants setup start rNext deltaBar hscales hdelta birth hbirth _ i B hBH
    hclock D hDR heta hsmall hthreshold hconstant hcanonical hpinch a ha hac
    hscalar hpast hnear V hVU hV d hdB inner hinitialInner
  by_contra hnot
  have hclim : D.lifetime < min d (a + tau) := lt_of_not_ge hnot
  have hcd : D.lifetime < d := hclim.trans_le (min_le_left _ _)
  have hctau : D.lifetime < a + tau := hclim.trans_le (min_le_right _ _)
  have hcB : D.lifetime < B := hcd.trans_le hdB
  have hcH : D.lifetime ≤ H := D.lifetime_le.trans hBH
  have haH : a ∈ Icc (0 : ℝ) H := ⟨ha, hac.le.trans hcH⟩
  have hR' : R0 ≤ D.radius := by rwa [hDR]
  have hcanonical' (s : ℝ) (hs : s ∈ Ico (0 : ℝ) D.lifetime)
      (y : (F.slice (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))).carrier)
      (hy : r⁻¹ ^ 2 ≤
        (F.connection (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))).scalarCurvature y) :
      SurgeryCanonicalControl F (birth + s / ((F.parameters.h birth)⁻¹ ^ 2)) y
        F.parameters.epsilon C := by
    rw [← hconstant]
    exact hcanonical _ (hclock s ⟨hs.1, hs.2.trans hcB⟩).1
      (D.cylinder.time_subset (mem_image_of_mem _ hs)) y hy
  have hnearCollar : ‖metricTwoJet
      (fun y => D.toCylinderCompactnessSample.coefficients (a, y)) x -
      metricTwoJet (standard.flow.metric a).euclideanCoefficients x‖ ≤ d1 :=
    (hnear x (Or.inr (mem_singleton x))).trans (min_le_left _ _)
  have hcurv (s : ℝ) (hs : s ∈ Ico (0 : ℝ) D.lifetime) (y) :
      (D.ordinary.flow.connection s).curvatureTensorNorm y ≤ K := by
    rcases le_total s a with hsa | has
    · exact (hpast s ⟨hs.1, hsa⟩ y).trans (le_max_left _ _)
    · let T := (s + D.lifetime) / 2
      have haT : a < T := by dsimp [T]; linarith only [has, hs.2]
      have hTc : T < D.lifetime := by dsimp [T]; linarith only [hs.2]
      have hsT : s ≤ T := by dsimp [T]; linarith only [hs.2]
      have hshort : T - a ≤ tau1 := by
        have h := min_le_left tau1 (sphereTolerance / (2 * (L + 1)))
        change tau ≤ tau1 at h
        linarith only [hTc, hctau, h]
      have h := hrestart F birth hbirth i D.toCylinderCompactnessSample hR'
        (heta.trans (min_le_left _ _)) D.region_open hsmall (r⁻¹ ^ 2) hthreshold
        hcanonical' hpinch a T ha haT hTc (hTc.le.trans hcH) hshort hscalar hpast
        _ (mem_image_of_mem _ haH) hnearCollar
      exact ((h.2 s ⟨has, hsT⟩ y).2).trans (le_max_right _ _)
  have hbirthBound : ∀ y ∈ D.chart.source,
      ‖(D.ordinary.flow.metric 0).pullbackCoefficients
        (targetChart D.chart D.target_point) y‖ ≤ Z := by
    intro y hy
    have hyR : y ∈ g0.metric.ball 0 R := by
      rwa [D.toCylinderCompactnessSample.source_eq, hDR] at hy
    have hyK : y ∈ closedBall := by
      change g0.metric.edist 0 y ≤ ENNReal.ofReal R
      exact le_of_lt hyR
    have hb := ((hcoeff _ _ _ _ _ D.toCylinderCompactnessSample.fixedComparison
      (heta.trans ((min_le_right _ _).trans (min_le_right _ _)))).2 y hyK).2 0 le_rfl
    dsimp only [CylinderCompactnessSample.fixedComparison] at hb
    rw [normalizedCoefficients_cast_initial D.standard_initial_eq D.comparison] at hb
    change ‖D.toCylinderCompactnessSample.coefficients (0, y)‖ ≤ Z
    rw [D.toCylinderCompactnessSample.initial_coefficients hy]
    simpa only [norm_iteratedFDeriv_zero] using hb
  have hball (z : UnitTwoSphere) : StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 R :=
    (hinside (Or.inl (mem_range_self z))).trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hsphereNear (s : ℝ) (hs : s ∈ Ico (0 : ℝ) D.lifetime) (has : a ≤ s)
      (z : UnitTwoSphere) :
      ‖metricTwoJet ((D.ordinary.flow.metric s).pullbackCoefficients
        (targetChart D.chart D.target_point)) (StandardCylinderPatch.sphereMap N z) -
        metricTwoJet (standard.flow.metric a).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ ≤ sphereTolerance := by
    let T := (s + D.lifetime) / 2
    have hT : 0 < T := by dsimp [T]; linarith only [hs.1, D.lifetime_pos]
    have hTc : T < D.lifetime := by dsimp [T]; linarith only [hs.2]
    have hsT : s ≤ T := by dsimp [T]; linarith only [hs.2]
    have haT : a ≤ T := has.trans hsT
    have hbounds := hest F D.standard_initial_eq birth hbirth i hR' D.radius_lt
      D.lifetime_pos D.comparison (heta.trans ((min_le_right _ _).trans (min_le_left _ _)))
      D.image_ball D.chart D.chart_source D.chart_eq D.cylinder D.chart_target_subset
      D.birth_identity D.ordinary D.target_point T hT hTc (hTc.le.trans hcH)
      (fun t ht => hcurv t ⟨ht.1, ht.2.trans_lt hTc⟩)
      (StandardCylinderPatch.sphereMap N z)
      (by rw [D.standard_initial_eq]; exact hinside (Or.inl (mem_range_self z)))
    have hmod := metricTwoJet_time_modulus
      (fun t => (D.ordinary.flow.metric t).pullbackCoefficients
        (targetChart D.chart D.target_point))
      (StandardCylinderPatch.sphereMap N z)
      (fun j hj => (hbounds.2 j hj).2 a ⟨ha, haT⟩ s ⟨hs.1, hsT⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr has)] at hmod
    have hLt : L * (s - a) ≤ sphereTolerance / 2 := by
      have htime : s - a ≤ sphereTolerance / (2 * (L + 1)) := by
        have htau' : tau ≤ sphereTolerance / (2 * (L + 1)) := min_le_right _ _
        linarith only [hs.2, hctau, htau']
      have hmul := (le_div_iff₀ hden).mp htime
      have hsa : 0 ≤ s - a := sub_nonneg.mpr has
      nlinarith only [hmul, hsa]
    calc
      _ ≤ ‖metricTwoJet ((D.ordinary.flow.metric s).pullbackCoefficients
          (targetChart D.chart D.target_point)) (StandardCylinderPatch.sphereMap N z) -
          metricTwoJet ((D.ordinary.flow.metric a).pullbackCoefficients
          (targetChart D.chart D.target_point)) (StandardCylinderPatch.sphereMap N z)‖ +
        ‖metricTwoJet ((D.ordinary.flow.metric a).pullbackCoefficients
          (targetChart D.chart D.target_point)) (StandardCylinderPatch.sphereMap N z) -
          metricTwoJet (standard.flow.metric a).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ sphereTolerance / 2 + sphereTolerance / 2 :=
        add_le_add (hmod.trans hLt)
          ((hnear _ (Or.inl (mem_range_self z))).trans (min_le_right _ _))
      _ = sphereTolerance := by ring
  have hh := F.parameters.h_pos birth (F.time_domain_nonnegative (F.surgery_times_subset hbirth))
  have hsource : D.chart.source = g0.metric.ball 0 R := by
    rw [D.toCylinderCompactnessSample.source_eq, hDR]
  have hremoved := maximal_cylinder_removal_of_bounds P hRpos hK hZpos hk hpinch O setup
    hscales hdelta hh D.cylinder D.lifetime_pos hcB hcH hclock D.birth_identity D.maximal
    D.chart hsource D.target_eq D.ordinary D.target_point hcurv hbirthBound N hball
    (fun z => metricTwoJet (standard.flow.metric a).euclideanCoefficients
      (StandardCylinderPatch.sphereMap N z)) hac (hsphereMargin a haH) hsphereNear
  exact not_disappears_of_surviving_subcylinder D.cylinder inner D.lifetime_pos hcd hVU hV
    hinitialInner hremoved.2

end PoincareConjecture.M44
