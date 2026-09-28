import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCompactnessFeed
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJetsConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_MovingJets












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance familySequenceCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance familySequenceCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {F : ℕ → SurgeryFlowData.{u}}
  {a : ℕ → ℝ} {ha : ∀ k, a k ∈ (F k).surgery_times}
  [∀ k, Nonempty ((F k).slice (a k)).carrier]
  {i : ∀ k, Fin ((F k).event (a k) (ha k)).cap_count}





theorem tendstoUniformlyOn_cylinder_standard_spatial_jets
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData g0)
    (unique : RepairedStandardCapUniquenessData g0 standard)
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {c K : ℝ} (hc1 : c ≤ 1)
    (hlim : Tendsto (fun k => (D k).lifetime) atTop (𝓝 c)) (hK : 0 < K)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    {b : ℝ} (hb : 0 ≤ b) (hbc : b < c) (m : ℕ) {C : Set E} (hC : IsCompact C) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (fun y => (D k).coefficients (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ m (standard.flow.metric p.1).euclideanCoefficients p.2)
      atTop (Icc (0 : ℝ) b ×ˢ C) := by
  obtain ⟨T, hbT, hTc⟩ := exists_between hbc
  have hT : 0 < T := hb.trans_lt hbT
  apply tendstoUniformlyOn_of_subsubsequence
  intro sigma hsigma
  have hRs := hR.comp hsigma.tendsto_atTop
  have hetas := heta.comp hsigma.tendsto_atTop
  have hlifes : ∀ᶠ k in atTop, T < (D (sigma k)).lifetime :=
    (hlim.comp hsigma.tendsto_atTop).eventually (lt_mem_nhds hTc)
  have hcurvs : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D (sigma k)).ordinary.flow.connection t).curvatureTensorNorm y ≤ K := by
    filter_upwards [hsigma.tendsto_atTop.eventually hcurv, hlifes] with k hk hklife
    intro t ht y
    exact hk t ⟨ht.1, ht.2.trans_lt hklife⟩ y
  obtain ⟨tau, htau, G, hG, hconv⟩ := exists_partial_standard_flow_of_cylinder_sequence
    P (fun k => D (sigma k)) hRs hetas hT hK hlifes hcurvs
  have hclosed := cylinder_subsequence_closed_spatial_jets P (fun k => D (sigma k))
    hRs hetas hT hK hlifes hcurvs htau G hconv hb hbT m hC
  refine ⟨tau, htau, ?_⟩
  apply tendstoUniformlyOn_partial_spatialJets_model unique G standard.flow m ?_ hclosed
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans_lt (hbc.trans_le hc1)⟩,
    by rw [hG]; exact hp.1.2.trans_lt hbT⟩





theorem eventually_cylinder_standard_spatial_jets
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData g0)
    (unique : RepairedStandardCapUniquenessData g0 standard)
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {H c K : ℝ} (hH : 0 < H) (hH1 : H < 1) (hc : 0 ≤ c) (hcH : c ≤ H)
    (hlife : ∀ k, (D k).lifetime ≤ H)
    (hlim : Tendsto (fun k => (D k).lifetime) atTop (𝓝 c)) (hK : 0 < K)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    (m : ℕ) {C : Set E} (hC : IsCompact C) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ x ∈ C,
        ‖iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x -
          iteratedFDeriv ℝ m (standard.flow.metric t).euclideanCoefficients x‖ < epsilon :=
  eventually_cylinder_moving_spatial_comparison P standard D hR heta hH hH1 hc hcH
    hlife hlim hK hcurv m hC (fun _ hb hbc =>
      tendstoUniformlyOn_cylinder_standard_spatial_jets P standard unique D hR heta
        (hcH.trans hH1.le) hlim hK hcurv hb hbc m hC)





theorem eventually_cylinder_standard_metricJetError_le
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData g0)
    (unique : RepairedStandardCapUniquenessData g0 standard)
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {H c K : ℝ} (hH : 0 < H) (hH1 : H < 1) (hc : 0 ≤ c) (hcH : c ≤ H)
    (hlife : ∀ k, (D k).lifetime ≤ H)
    (hlim : Tendsto (fun k => (D k).lifetime) atTop (𝓝 c)) (hK : 0 < K)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    (G : ℕ → ℝ → RiemannianMetric 3 E) (connections : ∀ k t, LeviCivitaData (G k t))
    (hmodel : ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime,
      G k t = standard.flow.metric t)
    (m : ℕ) {C : Set E} (hC : IsCompact C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, ∀ t ∈ Ico (0 : ℝ) (D k).lifetime, ∀ x ∈ C,
      singularMetricJetErrorSquared (G k t) (connections k t)
        (fun y v => (D k).coefficients (t, y) (v 0) (v 1)) m x ≤ epsilon / 2 := by
  apply eventually_standard_family_metricJetError_le_of_metric_eq standard.flow
    (by simpa only [standard.lifetime_one] using hH1) hC G connections hmodel m
    (fun k => (D k).chart.open_source)
    (eventually_cylinder_compact_subset_source D hR hC)
    (Eventually.of_forall (fun k t ht => ⟨ht.1, ht.2.le.trans (hlife k)⟩))
  · apply Eventually.of_forall
    intro k t ht
    exact (D k).coefficients_smooth.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hx => ⟨ht, hx⟩)
  · intro j _
    exact eventually_cylinder_standard_spatial_jets P standard unique D hR heta hH hH1
      hc hcH hlife hlim hK hcurv j hC
  · exact hepsilon

end PoincareConjecture.M44
