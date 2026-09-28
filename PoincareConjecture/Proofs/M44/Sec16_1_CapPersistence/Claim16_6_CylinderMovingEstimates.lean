import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCompactnessFeedData











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance movingEstimateCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance movingEstimateCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {F : ℕ → SurgeryFlowData.{u}}
  {a : ℕ → ℝ} {ha : ∀ k, a k ∈ (F k).surgery_times}
  [∀ k, Nonempty ((F k).slice (a k)).carrier]
  {i : ∀ k, Fin ((F k).event (a k) (ha k)).cap_count}





theorem eventually_cylinder_open_spatial_estimates
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {H K : ℝ} (hH : 0 < H) (hK : 0 < K)
    (hlife : ∀ k, (D k).lifetime ≤ H)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    {R : ℝ} (hRpos : 0 < R) (m : ℕ) :
    ∃ alpha Z L : ℝ, 0 < alpha ∧ 1 ≤ Z ∧ 0 ≤ L ∧ ∀ᶠ k in atTop,
      ∀ x ∈ g0.metric.ball 0 R,
        (∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ v : E,
          alpha * ‖v‖ ^ 2 ≤ (D k).coefficients (t, x) v v) ∧
        ∀ j ≤ m,
          (∀ t ∈ Ico (0 : ℝ) (D k).lifetime,
            ‖iteratedFDeriv ℝ j (fun y => (D k).coefficients (t, y)) x‖ ≤ Z) ∧
          (∀ s ∈ Ico (0 : ℝ) (D k).lifetime, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime,
            ‖iteratedFDeriv ℝ j (fun y => (D k).coefficients (t, y)) x -
              iteratedFDeriv ℝ j (fun y => (D k).coefficients (s, y)) x‖ ≤ L * |t - s|) := by
  obtain ⟨delta, alpha, Z, L, hdelta, halpha, hZ, hL, hestimate⟩ :=
    exists_cylinder_coordinate_estimates P g0 m (R0 := R + 2) (by linarith) hH hK
  refine ⟨alpha, Z, L, halpha, hZ, hL, ?_⟩
  filter_upwards [hR.eventually (eventually_ge_atTop (R + 2)),
    heta.eventually (gt_mem_nhds hdelta), hcurv] with k hkR hketa hkcurv
  intro x hx
  have hx' : x ∈ (F k).standard_initial.metric.ball 0 ((R + 2) - 2) := by
    simpa only [(D k).standard_initial_eq, add_sub_cancel_right] using hx
  have hpair (s : ℝ) (hs : s ∈ Ico (0 : ℝ) (D k).lifetime)
      (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (D k).lifetime) :
      (∀ v : E, alpha * ‖v‖ ^ 2 ≤ (D k).coefficients (s, x) v v) ∧
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => (D k).coefficients (s, y)) x‖ ≤ Z ∧
        ‖iteratedFDeriv ℝ j (fun y => (D k).coefficients (t, y)) x -
          iteratedFDeriv ℝ j (fun y => (D k).coefficients (s, y)) x‖ ≤ L * |t - s| := by
    let T := (max s t + (D k).lifetime) / 2
    have hmax : max s t < (D k).lifetime := max_lt hs.2 ht.2
    have hmax0 : 0 ≤ max s t := hs.1.trans (le_max_left _ _)
    have hT : 0 < T := by dsimp [T]; linarith only [hmax, hmax0]
    have hTB : T < (D k).lifetime := by dsimp [T]; linarith only [hmax]
    have hsT : s ≤ T := by
      have hsm : s ≤ max s t := le_max_left _ _
      dsimp [T]
      linarith only [hmax, hsm]
    have htT : t ≤ T := by
      have htm : t ≤ max s t := le_max_right _ _
      dsimp [T]
      linarith only [hmax, htm]
    have h := hestimate (F k) (D k).standard_initial_eq (a k) (ha k) (i k)
      hkR (D k).radius_lt (D k).lifetime_pos (D k).comparison hketa.le
      (D k).image_ball (D k).chart (D k).chart_source (D k).chart_eq
      (D k).cylinder (D k).chart_target_subset (D k).birth_identity
      (D k).ordinary (D k).target_point T hT hTB (hTB.le.trans (hlife k))
      (fun q hq y => hkcurv q ⟨hq.1, hq.2.trans_lt hTB⟩ y) x hx'
    exact ⟨h.1 s ⟨hs.1, hsT⟩, fun j hj =>
      ⟨(h.2 j hj).1 s ⟨hs.1, hsT⟩, (h.2 j hj).2 s ⟨hs.1, hsT⟩ t ⟨ht.1, htT⟩⟩⟩
  exact ⟨fun s hs => (hpair s hs s hs).1, fun j hj =>
    ⟨fun s hs => ((hpair s hs s hs).2 j hj).1,
      fun s hs t ht => ((hpair s hs t ht).2 j hj).2⟩⟩




theorem eventually_cylinder_open_jet_modulus
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {H K : ℝ} (hH : 0 < H) (hK : 0 < K)
    (hlife : ∀ k, (D k).lifetime ≤ H)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    (m : ℕ) {C : Set E} (hC : IsCompact C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in atTop,
      ∀ s ∈ Ico (0 : ℝ) (D k).lifetime, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime,
      ∀ x ∈ C,
        ‖iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x -
          iteratedFDeriv ℝ m (fun y => (D k).coefficients (s, y)) x‖ ≤ L * |t - s| := by
  obtain ⟨delta, hdelta, hdomain⟩ := exists_initial_comparison_domain_threshold g0 hC 0
  have hsub : C ⊆ g0.metric.ball 0 delta⁻¹ := (hdomain delta hdelta le_rfl).2
  obtain ⟨alpha, Z, L, _halpha, _hZ, hL, hest⟩ :=
    eventually_cylinder_open_spatial_estimates P D hR heta hH hK hlife hcurv
      (inv_pos.mpr hdelta) m
  refine ⟨L, hL, ?_⟩
  filter_upwards [hest] with k hk
  intro s hs t ht x hx
  exact ((hk x (hsub hx)).2 m le_rfl).2 s hs t ht

end PoincareConjecture.M44
