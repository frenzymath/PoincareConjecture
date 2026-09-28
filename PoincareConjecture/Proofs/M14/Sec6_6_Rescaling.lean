import PoincareConjecture.Proofs.M14.Sec6_6_RescalingJoint
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingStableTransport











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}




noncomputable def analyticRescalingData
    (hCoordinates : M12MetricPredecessors.{0} n) (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    M14AnalyticRescalingData G Q hQ a (rescalingTransport hM12 hM13 G Q hQ a) where
  chartedSpace_eq := rfl
  point_equiv := M13.parabolicSpacetimeIdentification G.spacetime Q hQ a
  point_equiv_eq := M13.parabolicSpacetimeIdentification_eq G.spacetime Q hQ a
  point_differential := M13.parabolicSpacetimeIdentification_derivative G.spacetime Q hQ a
  point_time := fun _ => rfl
  timeVector_map := by
    intro p
    change (show SpacetimeModelVector n from
      mfderiv (spacetimeModel n) (spacetimeModel n)
        (M13.parabolicSpacetimeIdentification G.spacetime Q hQ a) p
        (G.spacetime.timeVector p)) = Q • ((1 / Q : ℝ) • G.spacetime.timeVector p)
    rw [M13.parabolicSpacetimeIdentification_derivative]
    simp only [one_div, smul_smul, mul_inv_cancel₀ hQ.ne', one_smul]
  horizontal_map := M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
  horizontal_differential := by
    intro p v
    exact (M13.parabolicSpacetimeHorizontal_val G.spacetime Q hQ a p v).trans
      (M13.parabolicSpacetimeIdentification_derivative G.spacetime Q hQ a p v.val).symm
  horizontal_metric := M13.parabolicSpacetime_metric G.spacetime Q hQ a
  scalar_curvature := rescalingTransport_scalar hM12 hM13 G Q hQ a
  slice_identification := M13.parabolicSliceIdentification G.spacetime G.slices Q hQ a
  slice_identification_eq := M13.parabolicSliceIdentification_val G.spacetime G.slices Q hQ a
  slice_tangent := M13.parabolicSliceIdentification_tangent G.spacetime G.slices Q hQ a
  slice_metric := M13.parabolicSliceIdentification_metric G.spacetime G.slices Q hQ a
  initial_equiv := rescalingInitialEquiv G.spacetime Q hQ a
  initial_equiv_eq := fun _ _ => rfl
  initial_equiv_isometry := rescalingInitialEquiv_inner G.spacetime Q hQ a
  path_map := fun _ _ _ _ _ p => rescalingPath hM12 hM13 G Q hQ a p
  path_map_eq := fun _ _ _ _ _ p s => rescalingPath_curve hM12 hM13 G Q hQ a p s
  action_scale := fun _ _ _ _ _ p => rescalingPath_action hM12 hM13 G Q hQ a p
  path_inverse := by
    intro T τ₁ τ₂ x y p'
    exact ⟨rescalingPathInverse hM12 hM13 G Q hQ a p', fun _ => rfl⟩
  path_inverse_exact := by
    intro T τ₁ τ₂ x y p'
    exact ⟨rescalingPathInverse hM12 hM13 G Q hQ a p',
      rescalingPath_right_inverse hM12 hM13 G Q hQ a p'⟩
  path_minimizer_iff := fun _ _ _ _ _ p => rescalingPath_minimizing_iff hM12 hM13 G Q hQ a p
  path_inverse_action := by
    intro T τ₁ τ₂ x y p'
    let p := rescalingPathInverse hM12 hM13 G Q hQ a p'
    have heq := rescalingPath_right_inverse hM12 hM13 G Q hQ a p'
    refine ⟨p, heq, ?_⟩
    have h := rescalingPath_action hM12 hM13 G Q hQ a p
    rw [heq] at h
    exact h
  reduced_length_scale := fun _ _ _ _ _ hτ hfinite =>
    rescalingReducedLength hM12 hM13 G Q hQ a hτ hfinite
  density := rescalingDensity G
  density_eq := fun _ _ _ _ _ _ _ _ => rfl
  density' := rescalingDensity (rescalingTransport hM12 hM13 G Q hQ a)
  density'_eq := fun _ _ _ _ _ _ _ _ => rfl
  density_scale := fun _ _ _ _ hτ _ _ hfinite =>
    rescalingDensity_scale hM12 hM13 G Q hQ a hτ hfinite
  target_family := fun _ _ E => rescalingExponentialFamily hM12 hM13 G Q hQ a hM04 E
  exponential_domain_transport := fun _ _ E Z s =>
    rescalingExponential_domain_iff hCoordinates hM12 hM13 G Q hQ a E
      (rescalingExponentialFamily hM12 hM13 G Q hQ a hM04 E) Z s
  exponential_transport := fun _ _ E Z s hs =>
    rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E
      (rescalingExponentialFamily hM12 hM13 G Q hQ a hM04 E) Z s hs
  stable_transport := fun _ _ _ E H =>
    rescalingStableTransport hCoordinates hM12 hM13 G Q hQ a E
      (rescalingExponentialFamily hM12 hM13 G Q hQ a hM04 E) H
  joint_domain_transport := fun _ _ E Z s =>
    rescalingJointDomain_iff hCoordinates hM12 hM13 G Q hQ a E
      (rescalingExponentialFamily hM12 hM13 G Q hQ a hM04 E) Z s
  jacobian_data := fun _ _ _ _ H => measureJacobianData H





theorem analyticRescalingConclusion
    (hCoordinates : M12MetricPredecessors.{0} n) (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) : M14AnalyticRescalingConclusion G :=
  fun Q hQ a => ⟨rescalingTransport hM12 hM13 G Q hQ a,
    ⟨analyticRescalingData hCoordinates hM04 hM12 hM13 G Q hQ a⟩⟩

end PoincareConjecture.M14
