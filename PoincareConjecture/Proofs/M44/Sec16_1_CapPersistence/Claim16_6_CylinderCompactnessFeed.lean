import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCompactnessFeedJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitClosedJets












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance cylinderFeedAssemblyCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderFeedAssemblyCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {F : ℕ → SurgeryFlowData.{u}}
  {a : ℕ → ℝ} {ha : ∀ k, a k ∈ (F k).surgery_times}
  [∀ k, Nonempty ((F k).slice (a k)).carrier]
  {i : ∀ k, Fin ((F k).event (a k) (ha k)).cap_count}






theorem exists_partial_standard_flow_of_cylinder_sequence
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (hlife : ∀ᶠ k in atTop, T < (D k).lifetime)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ S : PartialStandardCapFlow g0,
      S.lifetime = T ∧ CompactSmoothConvergenceOn
        (fun k => (D (sigma k)).coefficients)
        (fun p => (S.flow.metric p.1).euclideanCoefficients p.2) atTop
        (Ioo 0 T ×ˢ univ) := by
  apply exists_rescaled_partial_flow_from_sequence g0 hT (fun k => (D k).coefficients)
  · exact fun R _ => eventually_cylinder_coefficients_smooth D hR hlife R
  · intro R hRpos C _hC hCU m
    obtain ⟨B, _hB, hbound⟩ :=
      eventually_cylinder_spacetime_jet_bound P D hR heta hT hK hlife hcurv hRpos m
    exact ⟨B, hbound.mono fun _ hk p hp => hk p (hCU hp)⟩
  · exact fun p _ => Eventually.of_forall fun k => (D k).coefficients_symmetric p
  · exact fun _ hp =>
      eventually_cylinder_coefficients_elliptic P D hR heta hT hK hlife hcurv hp
  · exact fun _ hp => eventually_cylinder_coefficients_evolution D hR hlife hp
  · intro m x
    exact (tendstoUniformlyOn_cylinder_initial_spatial_jet D hR heta m
      (isCompact_singleton (x := x))).tendsto_at (mem_singleton x)
  · intro m C hC
    obtain ⟨L, hL, hmod⟩ :=
      eventually_cylinder_birth_jet_modulus P D hR heta hT hK hlife hcurv m hC
    exact ⟨L, hL, fun t ht x hx => hmod.mono fun _ hk => hk t ht x hx⟩
  · intro T0 _hT0 hT0T
    refine ⟨K, hK.le, ?_⟩
    intro R _hRpos
    exact (eventually_cylinder_coefficient_curvature_bound D hR hcurv R).mono
      fun _ hk t ht x hx => hk t ⟨ht.1, ht.2.trans hT0T.le⟩ x hx





theorem cylinder_subsequence_closed_spatial_jets
    (P : M44CapPersistencePredecessors.{u})
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (hR : Tendsto (fun k => (D k).radius) atTop atTop)
    (heta : Tendsto (fun k => (D k).eta) atTop (𝓝 0))
    {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (hlife : ∀ᶠ k in atTop, T < (D k).lifetime)
    (hcurv : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ((D k).ordinary.flow.connection t).curvatureTensorNorm y ≤ K)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) (S : PartialStandardCapFlow g0)
    (hconv : CompactSmoothConvergenceOn
      (fun k => (D (sigma k)).coefficients)
      (fun p => (S.flow.metric p.1).euclideanCoefficients p.2) atTop
      (Ioo 0 T ×ˢ univ))
    {T0 : ℝ} (hT0 : 0 ≤ T0) (hT0T : T0 < T)
    (m : ℕ) {C : Set E} (hC : IsCompact C) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m
        (fun y => (D (sigma k)).coefficients (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ m (S.flow.metric p.1).euclideanCoefficients p.2)
      atTop (Icc 0 T0 ×ˢ C) := by
  apply tendstoUniformlyOn_rescaled_partial_flow_closed_jets S hT0 hT0T hconv m hC
  · intro W hW
    exact hsigma.tendsto_atTop.eventually
      (tendstoUniformlyOn_cylinder_initial_spatial_jet D hR heta m hC W hW)
  · obtain ⟨L, hL, hmod⟩ :=
      eventually_cylinder_birth_jet_modulus P D hR heta hT hK hlife hcurv m hC
    exact ⟨L, hL, hsigma.tendsto_atTop.eventually hmod⟩

end PoincareConjecture.M44
