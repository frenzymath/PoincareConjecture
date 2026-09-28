import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCompactnessFeedEstimates
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitCurvature











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance cylinderFeedJetCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderFeedJetCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {F : ℕ → SurgeryFlowData.{u}}
  {a : ℕ → ℝ} {ha : ∀ k, a k ∈ (F k).surgery_times}
  [∀ k, Nonempty ((F k).slice (a k)).carrier]
  {i : ∀ k, Fin ((F k).event (a k) (ha k)).cap_count}




theorem eventually_cylinder_spacetime_jet_bound
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (hlife : ∀ᶠ k in atTop, T < (D k).lifetime)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    {R : ℝ} (hRpos : 0 < R) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ p ∈ Ioo (0 : ℝ) T ×ˢ g0.metric.ball 0 R,
        ‖iteratedFDeriv ℝ m (D k).coefficients p‖ ≤ B := by
  let S (k : ℕ) : Set (ℝ × E) :=
    (Ioo (0 : ℝ) T ×ˢ g0.metric.ball 0 R) ∩
      (Ioo (0 : ℝ) (D k).lifetime ×ˢ (D k).chart.source)
  obtain ⟨alpha, _Z, _L, halpha, _hZ, _hL, hell⟩ :=
    eventually_cylinder_spatial_estimates P D hR heta hT hK hlife hcurv hRpos 0
  have helliptic : ∀ᶠ k in atTop, ∀ p ∈ S k, ∀ v : E,
      alpha * ‖v‖ ^ 2 ≤ (D k).coefficients p v v := by
    filter_upwards [hell] with k hk p hp v
    exact (hk p.2 hp.1.2).1 p.1 ⟨hp.1.1.1.le, hp.1.1.2.le⟩ v
  have hspatial : ∀ r : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ p ∈ S k, ∀ j ≤ r,
        ‖iteratedFDeriv ℝ j (fun x => (D k).coefficients (p.1, x)) p.2‖ ≤ B := by
    intro r
    obtain ⟨_alpha, Z, _L, _ha, hZ, _hL, hbound⟩ :=
      eventually_cylinder_spatial_estimates P D hR heta hT hK hlife hcurv hRpos r
    refine ⟨Z, zero_le_one.trans hZ, ?_⟩
    filter_upwards [hbound] with k hk p hp j hj
    exact ((hk p.2 hp.1.2).2 j hj).1 p.1 ⟨hp.1.1.1.le, hp.1.1.2.le⟩
  obtain ⟨B, hB, hbound⟩ := eventually_coordinate_spacetime_jet_bound atTop 3
    (fun k => (D k).coefficients) (fun k => Ioo 0 (D k).lifetime)
    (fun k => (D k).chart.source) S
    (fun k => (D k).coefficients_smooth.mono
      (prod_mono Ioo_subset_Ico_self Subset.rfl))
    (fun _ => isOpen_Ioo) (fun k => (D k).chart.open_source)
    (fun _ => inter_subset_right)
    (fun k p hp => (D k).coefficients_invertible p.1 hp.2)
    (fun k _ ht _ hx => (D k).coefficients_evolution ht hx)
    halpha helliptic hspatial m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, hlife, eventually_cylinder_ball_subset_source D hR R]
    with k hk hklife hsource
  intro p hp
  exact hk p ⟨hp, ⟨⟨hp.1.1, hp.1.2.trans hklife⟩, hsource hp.2⟩⟩




theorem eventually_cylinder_coefficients_elliptic
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (hlife : ∀ᶠ k in atTop, T < (D k).lifetime)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    {p : ℝ × E} (hp : p ∈ Ioo (0 : ℝ) T ×ˢ univ) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ k in atTop, ∀ v : E,
      alpha * ‖v‖ ^ 2 ≤ (D k).coefficients p v v := by
  obtain ⟨R, hRpos, hpoint⟩ :=
    exists_cylinder_feed_compact_radius g0 (isCompact_singleton (x := p.2))
  obtain ⟨alpha, _Z, _L, halpha, _hZ, _hL, hbound⟩ :=
    eventually_cylinder_spatial_estimates P D hR heta hT hK hlife hcurv hRpos 0
  exact ⟨alpha, halpha, hbound.mono fun _ hk =>
    (hk p.2 (hpoint (mem_singleton p.2))).1 p.1 ⟨hp.1.1.le, hp.1.2.le⟩⟩



theorem eventually_cylinder_coefficients_evolution
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    {T : ℝ} (hlife : ∀ᶠ k in atTop, T < (D k).lifetime)
    {p : ℝ × E} (hp : p ∈ Ioo (0 : ℝ) T ×ˢ univ) :
    ∀ᶠ k in atTop, HasDerivAt (fun t => (D k).coefficients (t, p.2))
      (ricciFlowOperator 3 (metricTwoJet (fun x => (D k).coefficients (p.1, x)) p.2)) p.1 := by
  filter_upwards [hlife,
    eventually_cylinder_compact_subset_source D hR (isCompact_singleton (x := p.2))]
    with k hklife hsource
  exact (D k).coefficients_evolution ⟨hp.1.1, hp.1.2.trans hklife⟩
    (hsource (mem_singleton p.2))




theorem eventually_cylinder_coefficient_curvature_bound
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    {T K : ℝ}
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K) (R : ℝ) :
    ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ g0.metric.ball 0 R,
      standardJetCurvatureNorm
        (metricTwoJet (fun y => (D k).coefficients (t, y)) x) ≤ K := by
  filter_upwards [hcurv, eventually_cylinder_ball_subset_source D hR R]
    with k hk hsource
  intro t ht x hx
  change standardJetCurvatureNorm (metricTwoJet
    (((D k).ordinary.flow.metric t).pullbackCoefficients
      (targetChart (D k).chart (D k).target_point)) x) ≤ K
  rw [standardJetCurvatureNorm_pullbackCoefficients
    ((D k).ordinary.flow.metric t) ((D k).ordinary.flow.connection t)
    (D k).chart.open_source (contMDiffOn_targetChart (D k).chart (D k).target_point)
    (fun _ hy => (D k).target_derivative_invertible hy) (hsource hx)]
  exact hk t ht _

end PoincareConjecture.M44
