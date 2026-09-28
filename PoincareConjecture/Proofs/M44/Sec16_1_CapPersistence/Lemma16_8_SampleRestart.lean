import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderBirthBuffer
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StoppedCylinderRestart











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance sampleRestartCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sampleRestartCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance sampleRestartTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance sampleRestartTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace





theorem exists_sample_restart_cutoff (P : M44CapPersistencePredecessors.{u})
    (g0 : StandardInitialMetric) (C0 : ℝ) (x u v : E)
    {model : Set (MetricTwoJet 3)} (hmodel : IsCompact model)
    (hmargin : model ⊆ collarJetRegion C0 u v)
    {R0 M Kpast H : ℝ} (hR0 : 2 < R0)
    (hx : x ∈ g0.metric.ball 0 (R0 - 2)) (hM : 0 < M) (hH : 0 < H) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
      ∀ (F : SurgeryFlowData.{u}) (birth : ℝ) (hbirth : birth ∈ F.surgery_times)
        [Nonempty (F.slice birth).carrier] (i : Fin (F.event birth hbirth).cap_count),
      ∀ D : CylinderCompactnessSample g0 F birth hbirth i,
      R0 ≤ D.radius → D.eta ≤ delta → IsOpen D.region →
      F.parameters.h birth ^ 2 ≤ 1 →
      ∀ q : ℝ, F.parameters.h birth ^ 2 * q ≤ M →
      (∀ s (_hs : s ∈ Ico (0 : ℝ) D.lifetime),
        ∀ y : (F.slice (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))).carrier,
        q ≤ (F.connection (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))).scalarCurvature y →
        SurgeryCanonicalControl F (birth + s / ((F.parameters.h birth)⁻¹ ^ 2)) y
          F.parameters.epsilon C0) → SurgeryFlowPinched F →
      ∀ a T : ℝ, 0 ≤ a → a < T → T < D.lifetime → T ≤ H → T - a ≤ tau →
      (∀ y, (D.ordinary.flow.connection a).scalarCurvature y ≤ M) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ y,
        (D.ordinary.flow.connection s).curvatureTensorNorm y ≤ Kpast) →
      ∀ J ∈ model, ‖metricTwoJet (fun y => D.coefficients (a, y)) x - J‖ ≤ delta →
      (∀ s ∈ Icc a T,
        metricTwoJet (fun y => D.coefficients (s, y)) x ∈ collarJetRegion C0 u v) ∧
      (∀ s ∈ Icc a T, ∀ y,
        (D.ordinary.flow.connection s).scalarCurvature y ≤ 2 * M ∧
        (D.ordinary.flow.connection s).curvatureTensorNorm y ≤
          13 * max (2 * M) (Real.exp 4)) := by
  obtain ⟨d0, alpha, Z, K0, hd0, halpha, hZ, hK0, hbuffer⟩ :=
    exists_cylinder_birth_buffer.{u} g0 hR0 2
  obtain ⟨d1, tau, hd1, htau, hrestart⟩ :=
    exists_stopped_cylinder_restart_bound P C0 u v hmodel hmargin hM
      (zero_lt_one.trans_le hK0) (Kpast := Kpast) hH (r := 1) zero_lt_one
      halpha (zero_le_one.trans hZ) hZ
  refine ⟨min d0 d1, tau, lt_min hd0 hd1, htau, ?_⟩
  intro F birth hbirth _ i D hR heta hU hsmall q hq hcanonical hpinch
    a T ha haT hTB hTH hshort hscalar hpast J hJ hnear
  obtain ⟨buffer⟩ := hbuffer F birth hbirth i D hR (heta.trans (min_le_left _ _))
  let V := g0.metric.ball 0 (R0 - 2)
  have hV : IsOpen V := by
    dsimp [V]
    rw [M36.standard_ball_eq_euclidean g0 (by linarith : 0 < R0 - 2)]
    exact Metric.isOpen_ball
  have hsub : V ⊆ buffer.chart.source := by
    rw [buffer.source_eq]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hconnected : IsPreconnected D.chart.target := by
    have hpre : IsPreconnected D.chart.source :=
      D.source_eq.symm ▸ g0.metric.isPreconnected_ball 0 D.radius
    have h := hpre.image D.chart D.chart.contMDiffOn.continuousOn
    rwa [D.chart.toPartialEquiv.image_source_eq_target] at h
  have hnormalizedSmall : (((F.parameters.h birth)⁻¹ ^ 2) : ℝ)⁻¹ ≤ 1 := by
    simpa only [inv_pow, inv_inv] using hsmall
  have hcanonical' (s : ℝ) (_hs : s ∈ Ico a T)
      (y : (⟨D.chart.target, D.chart.open_target⟩ : Opens (F.slice birth).carrier))
      (hhigh : F.parameters.h birth ^ 2 * q ≤
        (D.ordinary.flow.connection s).scalarCurvature y)
      (hsI : s ∈ Ico 0 D.lifetime) :
      SurgeryCanonicalControl F (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))
        (cylinderTargetTransport D.cylinder D.chart s hsI y) F.parameters.epsilon C0 := by
    apply hcanonical s hsI (cylinderTargetTransport D.cylinder D.chart s hsI y)
    rw [D.ordinary.scalar_eq hU D.chart_target_subset s hsI y] at hhigh
    apply (div_le_div_iff_of_pos_right D.cylinder.scale_pos).mp
    simpa only [div_eq_mul_inv, inv_pow, inv_inv, mul_comm] using hhigh
  have hnear' : ‖metricTwoJet ((D.ordinary.flow.metric a).pullbackCoefficients buffer.chart)
      x - J‖ ≤ d1 := by
    simpa only [buffer.map_eq, CylinderCompactnessSample.coefficients] using
      hnear.trans (min_le_right _ _)
  have h := hrestart F (F.slice birth) D.cylinder hU hnormalizedSmall D.chart
    D.chart_target_subset hconnected D.ordinary ha haT hTB hTH hshort hq hcanonical'
    hscalar hpast hpinch buffer.chart
    (fun j hj y hy => buffer.initial_curvature y hy j hj) hV hsub
    (fun y hy => (buffer.buffer y hy).1) (fun y hy => (buffer.buffer y hy).2)
    (fun y hy => (buffer.initial_bounds y (hsub hy)).1)
    (fun y hy => (buffer.initial_bounds y (hsub hy)).2.1)
    (fun y hy j hj => (buffer.initial_bounds y (hsub hy)).2.2 j (by omega))
    x hx J hJ hnear'
  simpa only [buffer.map_eq, CylinderCompactnessSample.coefficients] using h

end PoincareConjecture.M44
