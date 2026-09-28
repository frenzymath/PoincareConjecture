import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_SampleRestart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialScalarBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialTwoJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance initialSampleCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialSampleCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance initialSampleTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance initialSampleTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem CylinderCompactnessSample.initial_fixed_coefficients
    {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
    {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
    {i : Fin (F.event a ha).cap_count} (D : CylinderCompactnessSample g0 F a ha i)
    {x : E} (hx : x ∈ D.chart.source) :
    D.coefficients (0, x) = D.fixedComparison.normalizedCoefficients x := by
  dsimp only [CylinderCompactnessSample.fixedComparison]
  rw [normalizedCoefficients_cast_initial D.standard_initial_eq D.comparison]
  exact D.initial_coefficients hx

theorem exists_global_initial_sample_scalar_bound
    {g0 : StandardInitialMetric} (estimate : StandardCapEstimate g0) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (F : SurgeryFlowData.{u}) (a : ℝ)
      (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier]
      (i : Fin (F.event a ha).cap_count) (D : CylinderCompactnessSample g0 F a ha i),
      D.eta ≤ 1 / 4 → ∀ y, (D.ordinary.flow.connection 0).scalarCurvature y ≤ M := by
  obtain ⟨M, hM, hscalar⟩ := exists_global_initial_chart_scalar_bound.{u, u} estimate
  refine ⟨M, hM, ?_⟩
  intro F a ha _ i D heta
  have hsub : D.chart.source ⊆ g0.metric.ball 0 D.eta⁻¹ := by
    rw [D.source_eq]
    exact fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal D.radius_lt.le)
  have hlink : EqOn ((D.ordinary.flow.metric 0).pullbackCoefficients
      (targetPartialDiffeomorph D.chart D.target_point))
      D.fixedComparison.normalizedCoefficients D.chart.source :=
    fun _ hx => D.initial_fixed_coefficients hx
  exact fun y => hscalar _ _ _ _ _ D.fixedComparison heta
    (D.ordinary.flow.metric 0) (D.ordinary.flow.connection 0)
    (targetPartialDiffeomorph D.chart D.target_point) hsub hlink y (mem_univ y)

theorem initial_sample_curvature_bound (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
    {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
    {i : Fin (F.event a ha).cap_count} (D : CylinderCompactnessSample g0 F a ha i)
    (hU : IsOpen D.region) (hsmall : F.parameters.h a ^ 2 ≤ 1)
    (hpinch : SurgeryFlowPinched F) {M : ℝ}
    (hscalar : ∀ y, (D.ordinary.flow.connection 0).scalarCurvature y ≤ M) :
    ∀ y, (D.ordinary.flow.connection 0).curvatureTensorNorm y ≤
      13 * max M (Real.exp 4) := by
  intro y
  have hzero : (0 : ℝ) ∈ Ico 0 D.lifetime := ⟨le_rfl, D.lifetime_pos⟩
  have htime := D.cylinder.time_subset (mem_image_of_mem _ hzero)
  have hR : (((F.parameters.h a)⁻¹ ^ 2) : ℝ)⁻¹ *
      (F.connection (a + 0 / ((F.parameters.h a)⁻¹ ^ 2))).scalarCurvature
        (cylinderTargetTransport D.cylinder D.chart 0 hzero y) ≤ M := by
    simpa only [D.ordinary.scalar_eq hU D.chart_target_subset 0 hzero y,
      div_eq_mul_inv, mul_comm] using hscalar y
  have hnormalized : (((F.parameters.h a)⁻¹ ^ 2) : ℝ)⁻¹ ≤ 1 := by
    simpa only [inv_pow, inv_inv] using hsmall
  have h := (hpinch _ htime).scaled_curvature_norm_le P
    (mem_univ (cylinderTargetTransport D.cylinder D.chart 0 hzero y))
    (inv_pos.mpr D.cylinder.scale_pos).le hnormalized hR
  simpa only [D.ordinary.curvatureTensorNorm_eq hU D.chart_target_subset 0 hzero y,
    div_eq_mul_inv, mul_comm] using h

theorem exists_initial_sample_bound (P : M44CapPersistencePredecessors.{u})
    (g0 : StandardInitialMetric) (estimate : StandardCapEstimate g0)
    (C0 : ℝ) (x u v : E)
    (hcollar : metricTwoJet g0.metric.euclideanCoefficients x ∈ collarJetRegion C0 u v)
    {R0 : ℝ} (hR0 : 2 < R0) (hx : x ∈ g0.metric.ball 0 (R0 - 2)) :
    ∃ delta tau K : ℝ, 0 < delta ∧ 0 < tau ∧ 0 < K ∧
      ∀ (F : SurgeryFlowData.{u}) (birth : ℝ) (hbirth : birth ∈ F.surgery_times)
        [Nonempty (F.slice birth).carrier] (i : Fin (F.event birth hbirth).cap_count),
      ∀ D : CylinderCompactnessSample g0 F birth hbirth i,
      R0 ≤ D.radius → D.eta ≤ delta → IsOpen D.region →
      F.parameters.h birth ^ 2 ≤ 1 →
      ∀ q : ℝ, F.parameters.h birth ^ 2 * q ≤ 1 →
      (∀ s (_hs : s ∈ Ico (0 : ℝ) D.lifetime),
        ∀ y : (F.slice (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))).carrier,
        q ≤ (F.connection (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))).scalarCurvature y →
        SurgeryCanonicalControl F (birth + s / ((F.parameters.h birth)⁻¹ ^ 2)) y
          F.parameters.epsilon C0) → SurgeryFlowPinched F →
      ∀ s ∈ Ico (0 : ℝ) (min D.lifetime tau), ∀ y,
        (D.ordinary.flow.connection s).curvatureTensorNorm y ≤ K := by
  obtain ⟨M, hM, hscalar⟩ := exists_global_initial_sample_scalar_bound.{u} estimate
  let J := metricTwoJet g0.metric.euclideanCoefficients x
  obtain ⟨d0, tau, hd0, htau, hrestart⟩ := exists_sample_restart_cutoff P g0 C0 x u v
    (model := {J}) isCompact_singleton
    (by intro z hz; obtain rfl : z = J := hz; exact hcollar)
    hR0 hx (zero_lt_one.trans_le hM) (Kpast := 13 * max M (Real.exp 4))
    (H := 1) zero_lt_one
  obtain ⟨d1, hd1, hnear⟩ :=
    exists_initial_twoJet_cutoff.{u} g0 (isCompact_singleton (x := x)) hd0
  refine ⟨min d0 (min d1 (1 / 4)), min 1 tau, 13 * max (2 * M) (Real.exp 4),
    lt_min hd0 (lt_min hd1 (by norm_num)), lt_min zero_lt_one htau, by positivity, ?_⟩
  intro F birth hbirth _ i D hR heta hU hsmall q hq hcanonical hpinch
  have hscalar0 := hscalar F birth hbirth i D
    (heta.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpast : ∀ s ∈ Icc (0 : ℝ) 0, ∀ y,
      (D.ordinary.flow.connection s).curvatureTensorNorm y ≤ 13 * max M (Real.exp 4) := by
    intro s hs
    obtain rfl : s = 0 := le_antisymm hs.2 hs.1
    exact initial_sample_curvature_bound P D hU hsmall hpinch hscalar0
  have hxsource : x ∈ D.chart.source := by
    rw [D.source_eq]
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have heq : (fun y => D.coefficients (0, y)) =ᶠ[𝓝 x]
      D.fixedComparison.normalizedCoefficients :=
    eventually_of_mem (D.chart.open_source.mem_nhds hxsource)
      (fun _ hy => D.initial_fixed_coefficients hy)
  have htwo : metricTwoJet (fun y => D.coefficients (0, y)) x =
      metricTwoJet D.fixedComparison.normalizedCoefficients x := by
    simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  have hnear0 : ‖metricTwoJet (fun y => D.coefficients (0, y)) x - J‖ ≤ d0 := by
    rw [htwo]
    exact (hnear _ _ _ _ _ D.fixedComparison
      (heta.trans ((min_le_right _ _).trans (min_le_left _ _)))).2 x (mem_singleton x)
  intro s hs y
  obtain ⟨T, hsT, hTmin⟩ := exists_between hs.2
  have hT : 0 < T := hs.1.trans_lt hsT
  have hTB : T < D.lifetime := hTmin.trans_le (min_le_left _ _)
  have hTtau : T ≤ min 1 tau := hTmin.le.trans (min_le_right _ _)
  have hshort : T - 0 ≤ tau := by
    simpa only [sub_zero] using hTtau.trans (min_le_right 1 tau)
  have h := hrestart F birth hbirth i D hR (heta.trans (min_le_left _ _)) hU hsmall
    q (hq.trans hM) hcanonical hpinch 0 T le_rfl hT hTB
    (hTtau.trans (min_le_left _ _)) hshort hscalar0 hpast J (mem_singleton J) hnear0
  exact (h.2 s ⟨hs.1, hsT.le⟩ y).2

end PoincareConjecture.M44
