import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCompactnessFeedData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance birthBufferCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance birthBufferCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

structure CylinderBirthBuffer {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}}
    {a : ℝ} {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
    {i : Fin (F.event a ha).cap_count} (D : CylinderCompactnessSample g0 F a ha i)
    (R0 alpha Z K0 : ℝ) (m : ℕ) where

  chart : PartialDiffeomorph (𝓡 3) (𝓡 3) E
    (⟨D.chart.target, D.chart.open_target⟩ : Opens (F.slice a).carrier) ∞

  source_eq : chart.source = g0.metric.ball 0 R0

  map_eq : (chart : E → (⟨D.chart.target, D.chart.open_target⟩ : Opens (F.slice a).carrier)) =
    targetChart D.chart D.target_point

  initial_bounds : ∀ x ∈ chart.source,
    (∀ w : E, alpha * ‖w‖ ^ 2 ≤ (D.ordinary.flow.metric 0).pullbackCoefficients chart x w w) ∧
    (∀ w : E, (D.ordinary.flow.metric 0).pullbackCoefficients chart x w w ≤ Z * ‖w‖ ^ 2) ∧
    ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j ((D.ordinary.flow.metric 0).pullbackCoefficients chart) x‖ ≤ Z

  initial_curvature : ∀ y ∈ chart.target, ∀ j ≤ m,
    (D.ordinary.flow.connection 0).curvatureDerivativeNorm j y ≤ K0

  buffer : ∀ x ∈ g0.metric.ball 0 (R0 - 2),
    IsCompact (closure ((D.ordinary.flow.metric 0).ball (chart x) 1)) ∧
      closure ((D.ordinary.flow.metric 0).ball (chart x) 1) ⊆ chart.target

theorem exists_cylinder_birth_buffer (g0 : StandardInitialMetric)
    {R0 : ℝ} (hR0 : 2 < R0) (m : ℕ) :
    ∃ delta alpha Z K0 : ℝ, 0 < delta ∧ 0 < alpha ∧ 1 ≤ Z ∧ 1 ≤ K0 ∧
      ∀ (F : SurgeryFlowData.{u}) (a : ℝ) (ha : a ∈ F.surgery_times)
        [Nonempty (F.slice a).carrier] (i : Fin (F.event a ha).cap_count),
      ∀ D : CylinderCompactnessSample g0 F a ha i,
      R0 ≤ D.radius → D.eta ≤ delta → Nonempty (CylinderBirthBuffer D R0 alpha Z K0 m) := by
  let K := {x : E | g0.metric.edist 0 x ≤ ENNReal.ofReal R0}
  have hK : IsCompact K := M36.standard_closed_ball_compact g0 (by linarith)
  obtain ⟨delta, alpha, Z, K0, hdelta, halpha, hZ, hK0, hbounds⟩ :=
    exists_initial_chart_bounds.{u, u} g0 hK m
  refine ⟨delta, alpha, Z, K0, hdelta, halpha, hZ, hK0, ?_⟩
  intro F a ha _ i D hR heta
  have hg0 := D.standard_initial_eq
  subst g0
  let W := F.standard_initial.metric.ball 0 R0
  let V := F.standard_initial.metric.ball 0 (R0 - 2)
  have hW : IsOpen W := by
    dsimp [W]
    rw [M36.standard_ball_eq_euclidean F.standard_initial (by linarith : 0 < R0)]
    exact Metric.isOpen_ball
  have hVW : V ⊆ W := fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hWf : W ⊆ D.chart.source := by
    rw [D.chart_source]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal hR)
  let chart := restrictChart (targetPartialDiffeomorph D.chart D.target_point) hW hWf
  let N : GeneralizedSliceCarrier.{u} :=
    ⟨(⟨D.chart.target, D.chart.open_target⟩ : Opens (F.slice a).carrier), inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance⟩
  have hWK : W ⊆ K := by
    intro x hx
    change F.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal R0
    exact hx.le
  obtain ⟨hjets, hcurv, _⟩ := hbounds _ _ _ _ _ D.comparison heta
    N (D.ordinary.flow.metric 0) (D.ordinary.flow.connection 0) chart hWK
      (fun x hx => D.initial_coefficients (hWf hx))
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  let g := m01RescaledMetric (F.metric a) ((F.parameters.h a)⁻¹ ^ 2) hscale
  have hg (y) (v w) : g.inner y v w =
      (F.parameters.h a)⁻¹ ^ 2 * (F.metric a).inner y v w := rfl
  have himage (r : ℝ) (hr : 0 < r) (hrR : r ≤ D.radius) :
      D.chart '' F.standard_initial.metric.ball 0 r = g.ball ((F.event a ha).caps i).tip r :=
    physical_birth_chart_image_ball F a ha i hr (hrR.trans_lt D.radius_lt) D.comparison
      (D.image_ball r hr (hrR.trans D.radius_lt.le)) g hg D.chart
      (fun x _ => D.chart_eq x)
  have hcTarget : chart.target = Subtype.val ⁻¹' (D.chart '' W) :=
    targetChart_image_eq_preimage D.chart D.target_point hWf
  have hmetric (y : (⟨D.chart.target, D.chart.open_target⟩ : Opens (F.slice a).carrier)) (w) :
      g.inner y.1 (mfderiv (𝓡 3) (𝓡 3) Subtype.val y w)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val y w) ≤ (D.ordinary.flow.metric 0).inner y w w := by
    rw [D.ordinary.initial_metric_link ⟨le_rfl, D.lifetime_pos⟩
      D.chart_target_subset D.birth_identity, hg]
  refine ⟨⟨chart, rfl, rfl, hjets, hcurv, ?_⟩⟩
  intro y hy
  have hval : (chart y).1 = D.chart y :=
    targetChart_val D.chart D.target_point (hWf (hVW hy))
  have hinner : D.chart y ∈ g.ball ((F.event a ha).caps i).tip (R0 - 2) := by
    rw [← himage (R0 - 2) (by linarith) (by linarith)]
    exact mem_image_of_mem D.chart hy
  have hinside : closure (g.ball (chart y).1 1) ⊆ D.chart '' W := by
    rw [hval, himage R0 (by linarith) hR]
    exact g.closure_ball_subset_ball_of_margin (by linarith) zero_le_one (by linarith) hinner
  have hcompact : IsCompact (closure (g.ball (chart y).1 1)) :=
    (F.slices_compact a (F.surgery_times_subset ha)).of_isClosed_subset
      isClosed_closure (subset_univ _)
  refine ⟨isCompact_closure_ball_of_open_metric _ g (D.ordinary.flow.metric 0) hmetric
    (chart y) 1 hcompact
      (hinside.trans (by rintro _ ⟨z, hz, rfl⟩; exact D.chart.map_source (hWf hz))), ?_⟩
  rw [hcTarget]
  exact (closure_ball_subset_preimage_of_open_metric _ g (D.ordinary.flow.metric 0) hmetric
    (chart y) 1).trans (preimage_mono hinside)

end PoincareConjecture.M44
