import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_RemovalAlternative
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_MaximalSamples
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMovingModel











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance maximalAlternativeCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance maximalAlternativeCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance maximalAlternativeTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance maximalAlternativeTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace






theorem exists_maximal_cap_alternative_cutoff
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {A eta theta K : ℝ} (hA : 0 < A) (htheta0 : 0 ≤ theta)
    (htheta : theta < 1) (hK : 0 < K) :
    ∃ R0 accuracy : ℝ, ∃ compact : Set E,
      A < R0 ∧ 0 < accuracy ∧ IsCompact compact ∧ compact ⊆ g0.metric.ball 0 R0 ∧
      ∀ R : ℝ, R0 ≤ R → ∃ eta0 delta0 : ℝ, 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
        {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
        {start rNext deltaBar : ℝ},
      SurgeryFixedScalesOn setup F O start rNext deltaBar → deltaBar ≤ delta0 →
      ∀ (birth : ℝ) (hbirth : birth ∈ F.surgery_times)
        [Nonempty (F.slice birth).carrier] (i : Fin (F.event birth hbirth).cap_count),
      (∀ s ∈ Ico 0 (surgeryCapDuration birth O.H (F.parameters.h birth) theta),
        birth + s / ((F.parameters.h birth)⁻¹ ^ 2) ∈
          surgeryObservationInterval O ∩ Ici start) → SurgeryFlowPinched F →
      ∀ D : MaximalCapSample g0 F birth hbirth i
        (surgeryCapDuration birth O.H (F.parameters.h birth) theta),
      D.radius = R → D.eta ≤ eta0 →
      ((F.event birth hbirth).necks i).neck.epsilon ≤
        F.local_constants.comparison_delta D.eta →
      O.standard_flow.base.lifetime = 1 →
      (∀ s ∈ Ico (0 : ℝ) D.lifetime, ∀ y,
        (D.ordinary.flow.connection s).curvatureTensorNorm y ≤ K) →
      (∀ s ∈ Ico (0 : ℝ) D.lifetime, ∀ x ∈ compact,
        ‖metricTwoJet (fun y => D.toCylinderCompactnessSample.coefficients (s, y)) x -
          metricTwoJet (standard.flow.metric s).euclideanCoefficients x‖ ≤ accuracy) →
      (∃ bound : ℝ, bound < eta ^ 2 ∧
        ∀ s (hs : s ∈ Ico (0 : ℝ) D.lifetime),
        ∀ x ∈ F.standard_initial.metric.ball 0 A,
          singularMetricJetErrorSquared (O.standard_flow.metric s) (O.standard_flow.connection s)
            (fun y v => D.cylinder.pullbackInner s hs (D.chart y)
              (mfderiv (𝓡 3) (𝓡 3) D.chart y (v 0))
              (mfderiv (𝓡 3) (𝓡 3) D.chart y (v 1))) ⌊eta⁻¹⌋₊ x ≤ bound) →
      SurgeryCapPersistenceAlternative F O birth hbirth i A eta theta := by
  obtain ⟨length, center, N, sphereTolerance, hsphereTolerance, hmargin⟩ :=
    exists_standard_sphere_margin standard htheta0 htheta
  let compact := range (StandardCylinderPatch.sphereMap N)
  have hcompact : IsCompact compact :=
    isCompact_range (StandardCylinderPatch.sphereMap N).continuous
  obtain ⟨R0, _hR0, hAR0, hinside⟩ :=
    exists_standard_ball_containing_compact g0 hcompact A
  refine ⟨R0, sphereTolerance / 2, compact, hAR0, half_pos hsphereTolerance,
    hcompact, hinside, ?_⟩
  intro R hR
  have hRpos : 0 < R := (hA.trans hAR0).trans_le hR
  have hAR : A ≤ R := hAR0.le.trans hR
  let closedBall := {y : E | g0.metric.edist 0 y ≤ ENNReal.ofReal R}
  have hclosed : IsCompact closedBall := M36.standard_closed_ball_compact g0 hRpos.le
  obtain ⟨eta0, alpha, Z, heta0, _halpha, hZ, hcoeff⟩ :=
    exists_initial_comparison_metric_bounds.{u} g0 hclosed 0
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hk : (0 : ℝ) < 1 / 4 := by norm_num
  refine ⟨eta0, cylinderRemovalCutoff.{u} g0 (H := theta) hRpos hK hZpos hk,
    heta0, cylinderRemovalCutoff_pos.{u} g0 (H := theta) hRpos hK hZpos hk, ?_⟩
  intro F O constants setup start rNext deltaBar hscales hdelta birth hbirth _ i
    hclock hpinch D hDR heta hlink hlife hcurv hnear hjets
  have hh := F.parameters.h_pos birth (F.time_domain_nonnegative (F.surgery_times_subset hbirth))
  have hcTheta : D.lifetime ≤ theta := D.lifetime_le.trans (surgeryCapDuration_le hh)
  have hsource : D.chart.source = g0.metric.ball 0 R := by
    rw [D.toCylinderCompactnessSample.source_eq, hDR]
  have hfsource : D.chart.source = F.standard_initial.metric.ball 0 R := by
    rw [D.chart_source, hDR]
  have hfit : R < D.eta⁻¹ := by simpa only [hDR] using D.radius_lt
  have hregion : D.region =
      (F.metric birth).ball ((F.event birth hbirth).caps i).tip (F.parameters.h birth * R) := by
    rw [D.region_eq, hDR]
  let outer := restrictCylinderSource D.cylinder (le_of_eq hregion.symm)
  have hinitial : ∀ hs x,
      x ∈ (F.metric birth).ball ((F.event birth hbirth).caps i).tip
        (F.parameters.h birth * R) → HEq (outer.forward 0 hs x) x :=
    fun hs x hx => D.birth_identity hs x (hregion.symm ▸ hx)
  have hstop : D.lifetime = surgeryCapDuration birth O.H (F.parameters.h birth) theta ∨
      birth + D.lifetime / ((F.parameters.h birth)⁻¹ ^ 2) ∈ F.surgery_times ∧
      SurgeryBallDisappearsAt F outer
        (birth + D.lifetime / ((F.parameters.h birth)⁻¹ ^ 2)) := by
    by_cases heq : D.lifetime = surgeryCapDuration birth O.H (F.parameters.h birth) theta
    · exact Or.inl heq
    · have hcB := lt_of_le_of_ne D.lifetime_le heq
      have hbirthBound : ∀ y ∈ D.chart.source,
          ‖(D.ordinary.flow.metric 0).pullbackCoefficients
            (targetChart D.chart D.target_point) y‖ ≤ Z := by
        intro y hy
        have hyR : y ∈ g0.metric.ball 0 R := hsource ▸ hy
        have hyK : y ∈ closedBall := by
          change g0.metric.edist 0 y ≤ ENNReal.ofReal R
          exact le_of_lt hyR
        have hb := ((hcoeff _ _ _ _ _ D.toCylinderCompactnessSample.fixedComparison
          heta).2 y hyK).2 0 le_rfl
        dsimp only [CylinderCompactnessSample.fixedComparison] at hb
        rw [normalizedCoefficients_cast_initial D.standard_initial_eq D.comparison] at hb
        change ‖D.toCylinderCompactnessSample.coefficients (0, y)‖ ≤ Z
        rw [D.toCylinderCompactnessSample.initial_coefficients hy]
        simpa only [norm_iteratedFDeriv_zero] using hb
      have hball (z : UnitTwoSphere) :
          StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 R :=
        (hinside (mem_range_self z)).trans_le (ENNReal.ofReal_le_ofReal hR)
      obtain ⟨s0, hs0, htail⟩ := exists_terminal_sphere_twoJet_tail standard htheta N
        hsphereTolerance D.lifetime_pos hcTheta
        (fun s y => D.toCylinderCompactnessSample.coefficients (s, y))
        (fun s hs z => hnear s hs _ (mem_range_self z))
      have hremoved := maximal_cylinder_removal_of_bounds P hRpos hK hZpos hk hpinch O setup
        hscales hdelta hh D.cylinder D.lifetime_pos hcB hcTheta hclock D.birth_identity D.maximal
        D.chart hsource D.target_eq D.ordinary D.target_point hcurv hbirthBound N hball
        (fun z => metricTwoJet (standard.flow.metric D.lifetime).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)) hs0
        (hmargin D.lifetime ⟨D.lifetime_pos.le, hcTheta⟩) htail
      exact Or.inr ⟨hremoved.1, disappears_restrict_source hremoved.2 (le_of_eq hregion.symm)⟩
  exact cap_persistence_alternative_of_enlarged_cylinder F O birth hbirth i hA hAR hfit htheta
    D.lifetime_pos D.lifetime_le outer hinitial D.comparison hlink D.image_ball
    D.chart hfsource D.chart_eq hlife hjets hstop

end PoincareConjecture.M44
