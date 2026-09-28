import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCompactnessFeedData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance cylinderFeedEstimateCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderFeedEstimateCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

theorem exists_cylinder_feed_compact_radius (g0 : StandardInitialMetric)
    {C : Set E} (hC : IsCompact C) :
    ∃ R : ℝ, 0 < R ∧ C ⊆ g0.metric.ball 0 R := by
  obtain ⟨delta, hdelta, hdomain⟩ := exists_initial_comparison_domain_threshold g0 hC 0
  exact ⟨delta⁻¹, inv_pos.mpr hdelta, (hdomain delta hdelta le_rfl).2⟩

variable {g0 : StandardInitialMetric} {F : ℕ → SurgeryFlowData.{u}}
  {a : ℕ → ℝ} {ha : ∀ k, a k ∈ (F k).surgery_times}
  [∀ k, Nonempty ((F k).slice (a k)).carrier]
  {i : ∀ k, Fin ((F k).event (a k) (ha k)).cap_count}

theorem eventually_cylinder_ball_subset_source
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop) (R : ℝ) :
    ∀ᶠ k in atTop, g0.metric.ball 0 R ⊆ (D k).chart.source := by
  filter_upwards [hR.eventually (eventually_ge_atTop R)] with k hk
  rw [(D k).source_eq]
  exact fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hk)

theorem eventually_cylinder_compact_subset_source
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    {C : Set E} (hC : IsCompact C) :
    ∀ᶠ k in atTop, C ⊆ (D k).chart.source := by
  obtain ⟨R, _hR, hCR⟩ := exists_cylinder_feed_compact_radius g0 hC
  exact (eventually_cylinder_ball_subset_source D hR R).mono fun _ h => hCR.trans h

theorem eventually_cylinder_coefficients_smooth
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    {T : ℝ} (hlife : ∀ᶠ k in atTop, T < (D k).lifetime) (R : ℝ) :
    ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (D k).coefficients
      (Ioo 0 T ×ˢ g0.metric.ball 0 R) := by
  filter_upwards [hlife, eventually_cylinder_ball_subset_source D hR R] with k hk hsource
  exact (D k).coefficients_smooth.mono
    (prod_mono (fun _ ht => ⟨ht.1.le, ht.2.trans hk⟩) hsource)

theorem eventually_cylinder_spatial_estimates
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (hlife : ∀ᶠ k in atTop, T < (D k).lifetime)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    {R : ℝ} (hRpos : 0 < R) (m : ℕ) :
    ∃ alpha Z L : ℝ, 0 < alpha ∧ 1 ≤ Z ∧ 0 ≤ L ∧ ∀ᶠ k in atTop,
      ∀ x ∈ g0.metric.ball 0 R,
        (∀ t ∈ Icc (0 : ℝ) T, ∀ v : E,
          alpha * ‖v‖ ^ 2 ≤ (D k).coefficients (t, x) v v) ∧
        ∀ j ≤ m,
          (∀ t ∈ Icc (0 : ℝ) T,
            ‖iteratedFDeriv ℝ j (fun y => (D k).coefficients (t, y)) x‖ ≤ Z) ∧
          (∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
            ‖iteratedFDeriv ℝ j (fun y => (D k).coefficients (t, y)) x -
              iteratedFDeriv ℝ j (fun y => (D k).coefficients (s, y)) x‖ ≤ L * |t - s|) := by
  obtain ⟨delta, alpha, Z, L, hdelta, halpha, hZ, hL, hestimate⟩ :=
    exists_cylinder_coordinate_estimates P g0 m (R0 := R + 2) (by linarith) hT hK
  refine ⟨alpha, Z, L, halpha, hZ, hL, ?_⟩
  filter_upwards [hR.eventually (eventually_ge_atTop (R + 2)),
    heta.eventually (gt_mem_nhds hdelta), hlife, hcurv] with k hkR hketa hklife hkcurv
  intro x hx
  have hx' : x ∈ (F k).standard_initial.metric.ball 0 ((R + 2) - 2) := by
    simpa only [(D k).standard_initial_eq, add_sub_cancel_right] using hx
  exact hestimate (F k) (D k).standard_initial_eq (a k) (ha k) (i k)
    hkR (D k).radius_lt (D k).lifetime_pos (D k).comparison hketa.le
    (D k).image_ball (D k).chart (D k).chart_source (D k).chart_eq
    (D k).cylinder (D k).chart_target_subset (D k).birth_identity
    (D k).ordinary (D k).target_point T hT hklife le_rfl hkcurv x hx'

theorem tendstoUniformlyOn_cylinder_initial_spatial_jet
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    (m : ℕ) {C : Set E} (hC : IsCompact C) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y => (D k).coefficients (0, y)))
      (iteratedFDeriv ℝ m g0.metric.euclideanCoefficients) atTop C := by
  have hconv := tendstoUniformlyOn_initial_coefficient_jets g0
    (fun k => (((F k).event (a k) (ha k)).local_result (i k)).output)
    (fun k => (((F k).event (a k) (ha k)).local_result (i k)).metric)
    (fun k => (((F k).event (a k) (ha k)).local_result (i k)).tip)
    (fun k => (((F k).event (a k) (ha k)).necks (i k)).neck.scale)
    (fun k => (D k).eta) (fun k => (D k).fixedComparison) heta m hC
  apply hconv.congr
  filter_upwards [eventually_cylinder_compact_subset_source D hR hC] with k hk
  intro x hx
  dsimp only [CylinderCompactnessSample.fixedComparison]
  rw [normalizedCoefficients_cast_initial (D k).standard_initial_eq (D k).comparison]
  exact ((D k).initial_spatial_jet (hk hx) m).symm

theorem eventually_cylinder_birth_jet_modulus
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (hlife : ∀ᶠ k in atTop, T < (D k).lifetime)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    (m : ℕ) {C : Set E} (hC : IsCompact C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in atTop, ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ C,
      ‖iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x -
        iteratedFDeriv ℝ m (fun y => (D k).coefficients (0, y)) x‖ ≤ L * t := by
  obtain ⟨R, hRpos, hCR⟩ := exists_cylinder_feed_compact_radius g0 hC
  obtain ⟨alpha, Z, L, _halpha, _hZ, hL, hbound⟩ :=
    eventually_cylinder_spatial_estimates P D hR heta hT hK hlife hcurv hRpos m
  refine ⟨L, hL, ?_⟩
  filter_upwards [hbound] with k hk
  intro t ht x hx
  have h := ((hk x (hCR hx)).2 m le_rfl).2
    0 ⟨le_rfl, hT.le⟩ t ⟨ht.1.le, ht.2.le⟩
  simpa only [sub_zero, abs_of_pos ht.1] using h

end PoincareConjecture.M44
