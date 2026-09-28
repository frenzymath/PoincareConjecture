import PoincareConjecture.Proofs.M44.Mathlib.MovingTimeComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderMovingEstimates
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCompactnessFeedEstimates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance movingJetsCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance movingJetsCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {F : ℕ → SurgeryFlowData.{u}}
  {a : ℕ → ℝ} {ha : ∀ k, a k ∈ (F k).surgery_times}
  [∀ k, Nonempty ((F k).slice (a k)).carrier]
  {i : ∀ k, Fin ((F k).event (a k) (ha k)).cap_count}




theorem eventually_cylinder_moving_spatial_comparison
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData g0)
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {H c K : ℝ} (hH : 0 < H) (hH1 : H < 1) (hc : 0 ≤ c) (hcH : c ≤ H)
    (hlife : ∀ k, (D k).lifetime ≤ H)
    (hlim : Tendsto (fun k => (D k).lifetime) atTop (𝓝 c)) (hK : 0 < K)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    (m : ℕ) {C : Set E} (hC : IsCompact C)
    (hinterior : ∀ b : ℝ, 0 ≤ b → b < c → TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (fun y => (D k).coefficients (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ m (standard.flow.metric p.1).euclideanCoefficients p.2)
      atTop (Icc (0 : ℝ) b ×ˢ C)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ x ∈ C,
        ‖iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x -
          iteratedFDeriv ℝ m (standard.flow.metric t).euclideanCoefficients x‖ < epsilon := by
  obtain ⟨L, hL, hmod⟩ := eventually_cylinder_open_jet_modulus P D hR heta hH hK
    hlife hcurv m hC
  have hid (g : RiemannianMetric 3 E) : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext y v w
    simp only [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  have hsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      (standard.flow.metric p.1).euclideanCoefficients p.2)
      (Ico 0 standard.flow.base.lifetime ×ˢ univ) := by
    simpa only [hid, MaximalStandardCapFlow.metric] using
      contDiffOn_pullbackCoefficients_within standard.flow.base.flow
      isOpen_univ (contMDiff_id.contMDiffOn (s := univ))
  have hsub : Icc (0 : ℝ) H ⊆ Ico (0 : ℝ) standard.flow.base.lifetime := by
    rw [standard.lifetime_one]
    exact fun _ ht => ⟨ht.1, ht.2.trans_lt hH1⟩
  have hcont : ContinuousOn (fun p : ℝ × E =>
      iteratedFDeriv ℝ m (standard.flow.metric p.1).euclideanCoefficients p.2)
      (Icc (0 : ℝ) H ×ˢ C) :=
    (contDiffOn_spatialJet_within hsmooth (uniqueDiffOn_Ico 0 standard.flow.base.lifetime)
      isOpen_univ m).continuousOn.mono (prod_mono hsub (subset_univ C))
  have hbirth : TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ m (fun y => (D k).coefficients (0, y)) x)
      (fun x => iteratedFDeriv ℝ m (standard.flow.metric 0).euclideanCoefficients x)
      atTop C := by
    simpa only [MaximalStandardCapFlow.metric, standard.flow.base.initial_metric] using
      tendstoUniformlyOn_cylinder_initial_spatial_jet D hR heta m hC
  have hmod' : ∀ᶠ k in atTop, ∀ s ∈ Ico (0 : ℝ) (D k).lifetime,
      ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ x ∈ C,
      dist (iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x)
        (iteratedFDeriv ℝ m (fun y => (D k).coefficients (s, y)) x) ≤ L * |t - s| := by
    simpa only [dist_eq_norm] using hmod
  simpa only [dist_eq_norm] using Poincare.uniformly_close_on_moving_initial_intervals
    hC hc hcH hL hlim hlife hcont hbirth hinterior hmod'

end PoincareConjecture.M44
