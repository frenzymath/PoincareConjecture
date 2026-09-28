import PoincareConjecture.Proofs.M14.Sec6_6_RescalingStable
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingMeasureBasis










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

private theorem horizontal_pair_cast {S : GeneralizedLGeometryTransport n X time I}
    {x p q : S.Point} (h : p = q) (L : S.Horizontal x →L[ℝ] S.Horizontal p)
    (v w : S.Horizontal x) :
    S.spacetime.horizontalMetric.inner q ((h ▸ L) v) ((h ▸ L) w) =
      S.spacetime.horizontalMetric.inner p (L v) (L w) := by
  cases h
  rfl

private theorem rescaled_pair_of_values (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (p q : S.Point) (hp : q = p)
    (v w : S.Horizontal p)
    (v' w' : (M13.parabolicSpacetime S Q hQ a).Horizontal q)
    (hv : (show SpacetimeModelVector n from v'.val) = v.val)
    (hw : (show SpacetimeModelVector n from w'.val) = w.val) :
    (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner q v' w' =
      Q * S.horizontalMetric.inner p v w := by
  subst q
  have hv' : v' = M13.parabolicSpacetimeHorizontal S Q hQ a p v := Subtype.ext hv
  have hw' : w' = M13.parabolicSpacetimeHorizontal S Q hQ a p w := Subtype.ext hw
  rw [hv', hw']
  exact M13.parabolicSpacetime_metric S Q hQ a p v w



theorem rescalingEndpointTangent_pair {T τ : ℝ} {x : G.Point}
    {E : M14ExponentialFamily G T x} (H : M14StableSet G T τ x E)
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) (v w : G.Horizontal x) :
    (G.slices (T - τ)).metricOnPoints.inner (H.endpoint_slice_map Z)
      (M14EndpointTangentDifferential G Z hZ v) (M14EndpointTangentDifferential G Z hZ w) =
      G.spacetime.horizontalMetric.inner (E.gamma Z (Real.sqrt τ))
        (E.differential Z (Real.sqrt τ) (H.survivor Z hZ) v)
        (E.differential Z (Real.sqrt τ) (H.survivor Z hZ) w) := by
  unfold M14EndpointTangentDifferential
  rw [(G.slices (T - τ)).metric_eq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [horizontal_pair_cast (H.endpoint_slice_map_val Z hZ).symm]
  have h := horizontal_pair_cast (H.endpoint_map_eq Z hZ) (H.endpoint_differential Z hZ) v w
  rw [H.endpoint_differential_eq] at h
  exact h.symm

include hCoordinates in


theorem rescalingDifferential_pair {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z v w : G.Horizontal x) (s s' : ℝ)
    (ht : s' = Real.sqrt Q * s)
    (hs : (Z, s) ∈ E.domain)
    (hs' : (rescalingInitialEquiv G.spacetime Q hQ a x Z, s') ∈ E'.domain) :
    (rescalingTransport hM12 hM13 G Q hQ a).spacetime.horizontalMetric.inner
      (E'.gamma (rescalingInitialEquiv G.spacetime Q hQ a x Z) s')
      (E'.differential (rescalingInitialEquiv G.spacetime Q hQ a x Z) s'
        hs' (rescalingInitialEquiv G.spacetime Q hQ a x v))
      (E'.differential (rescalingInitialEquiv G.spacetime Q hQ a x Z) s'
        hs' (rescalingInitialEquiv G.spacetime Q hQ a x w)) =
      Q * G.spacetime.horizontalMetric.inner (E.gamma Z s)
        (E.differential Z s hs v) (E.differential Z s hs w) := by
  subst s'
  exact rescaled_pair_of_values G.spacetime Q hQ a _ _
    (rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E E' Z s hs) _ _ _ _
    (rescalingDifferential_val hCoordinates hM12 hM13 G Q hQ a E E' Z v s hs hs')
    (rescalingDifferential_val hCoordinates hM12 hM13 G Q hQ a E E' Z w s hs hs')

include hCoordinates in



theorem rescalingStableTangent_pair {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E') (Z v w : G.Horizontal x)
    (hZ : Z ∈ H.carrier)
    (hZ' : rescalingInitialEquiv G.spacetime Q hQ a x Z ∈ H'.carrier) :
    ((rescalingTransport hM12 hM13 G Q hQ a).slices
        (parabolicTime Q a T - Q * τ)).metricOnPoints.inner
          (H'.endpoint_slice_map (rescalingInitialEquiv G.spacetime Q hQ a x Z))
          (M14EndpointTangentDifferential _ _ hZ'
            (rescalingInitialEquiv G.spacetime Q hQ a x v))
          (M14EndpointTangentDifferential _ _ hZ'
            (rescalingInitialEquiv G.spacetime Q hQ a x w)) =
      Q * (G.slices (T - τ)).metricOnPoints.inner (H.endpoint_slice_map Z)
        (M14EndpointTangentDifferential G Z hZ v) (M14EndpointTangentDifferential G Z hZ w) := by
  have htarget := rescalingEndpointTangent_pair (rescalingTransport hM12 hM13 G Q hQ a)
    H' _ hZ' (rescalingInitialEquiv G.spacetime Q hQ a x v)
      (rescalingInitialEquiv G.spacetime Q hQ a x w)
  have hsource := rescalingEndpointTangent_pair G H Z hZ v w
  exact htarget.trans
    ((rescalingDifferential_pair hCoordinates hM12 hM13 G Q hQ a E E' Z v w
      (Real.sqrt τ) (Real.sqrt (Q * τ)) (Real.sqrt_mul hQ.le τ)
        (H.survivor Z hZ) (H'.survivor _ hZ')).trans (congrArg (Q * ·) hsource.symm))

include hCoordinates in


theorem rescalingJacobian_scale {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E')
    (D : M14MeasureJacobianData G T τ x E H)
    (D' : M14MeasureJacobianData (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E' H')
    (hb : D'.sourceBasis = D.sourceBasis.map
      (rescalingInitialEquiv G.spacetime Q hQ a x).toLinearEquiv)
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier)
    (hZ' : rescalingInitialEquiv G.spacetime Q hQ a x Z ∈ H'.carrier) :
    D'.jacobian (rescalingInitialEquiv G.spacetime Q hQ a x Z) =
      Real.rpow Q ((n : ℝ) / 2) * D.jacobian Z := by
  rw [D'.jacobian_eq _ hZ', D.jacobian_eq _ hZ, hb]
  unfold M14MetricJacobianFromBasis
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    (G.slices (T - τ)).metricOnPoints.inner (H.endpoint_slice_map Z)
      (M14EndpointTangentDifferential G Z hZ (D.sourceBasis i))
      (M14EndpointTangentDifferential G Z hZ (D.sourceBasis j))
  have hmatrix : (fun i j : Fin n =>
      ((rescalingTransport hM12 hM13 G Q hQ a).slices
        (parabolicTime Q a T - Q * τ)).metricOnPoints.inner
        (H'.endpoint_slice_map (rescalingInitialEquiv G.spacetime Q hQ a x Z))
        (M14EndpointTangentDifferential _ _ hZ'
          ((D.sourceBasis.map (rescalingInitialEquiv G.spacetime Q hQ a x).toLinearEquiv) i))
        (M14EndpointTangentDifferential _ _ hZ'
          ((D.sourceBasis.map (rescalingInitialEquiv G.spacetime Q hQ a x).toLinearEquiv) j))) =
      Q • M := by
    funext i j
    exact rescalingStableTangent_pair hCoordinates hM12 hM13 G Q hQ a E E' H H'
      Z (D.sourceBasis i) (D.sourceBasis j) hZ hZ'
  refine (congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => Real.sqrt (max 0 N.det)) hmatrix).trans ?_
  change Real.sqrt (max 0 (Q • M).det) = Real.rpow Q ((n : ℝ) / 2) * Real.sqrt (max 0 M.det)
  rw [Matrix.det_smul, Fintype.card_fin]
  have hmax : max 0 (Q ^ n * M.det) = Q ^ n * max 0 M.det := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg hQ.le n), mul_zero]
  rw [hmax, Real.sqrt_mul (pow_nonneg hQ.le n)]
  have hfactor : Real.sqrt (Q ^ n) = Real.rpow Q ((n : ℝ) / 2) := by
    change Real.sqrt (Q ^ n) = Q ^ ((n : ℝ) / 2)
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [hfactor]

end PoincareConjecture.M14
