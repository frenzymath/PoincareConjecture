import PoincareConjecture.Proofs.M14.Sec6_6_RescalingStable
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingSliceVolume
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingActionValue
import PoincareConjecture.Proofs.M14.Sec6_7_MeasureTransport

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

theorem rescalingBackwardTime (T τ : ℝ) :
    parabolicTime Q a T - Q * τ = parabolicTime Q a (T - τ) := by
  unfold parabolicTime
  ring

include hCoordinates in

theorem rescalingStableEndpoint {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E') (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) :
    rescalingSliceAt hM12 hM13 G Q hQ a (T - τ) (parabolicTime Q a T - Q * τ)
        (rescalingBackwardTime Q a T τ) (H.endpoint_slice_map Z) =
      H'.endpoint_slice_map (rescalingInitialEquiv G.spacetime Q hQ a x Z) := by
  have hZ' := (rescalingStable_carrier_iff hCoordinates hM12 hM13 G Q hQ a E E' H H' Z).mp hZ
  apply Subtype.ext
  rw [rescalingSliceAt_val, H.endpoint_slice_map_val Z hZ, H.endpoint_map_eq Z hZ,
    H'.endpoint_slice_map_val _ hZ', H'.endpoint_map_eq _ hZ']
  simpa only [Real.sqrt_mul hQ.le] using
    (rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E E'
      Z (Real.sqrt τ) (H.survivor Z hZ)).symm

include hCoordinates in

theorem rescalingStableImage {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E') :
    (rescalingSliceAt hM12 hM13 G Q hQ a (T - τ) (parabolicTime Q a T - Q * τ)
      (rescalingBackwardTime Q a T τ)) '' (H.endpoint_slice_map '' H.carrier) =
        H'.endpoint_slice_map '' H'.carrier := by
  let A := rescalingInitialEquiv G.spacetime Q hQ a x
  ext q
  constructor
  · rintro ⟨p, ⟨Z, hZ, rfl⟩, rfl⟩
    refine ⟨A Z,
      (rescalingStable_carrier_iff hCoordinates hM12 hM13 G Q hQ a E E' H H' Z).mp hZ, ?_⟩
    exact (rescalingStableEndpoint hCoordinates hM12 hM13 G Q hQ a E E' H H' Z hZ).symm
  · rintro ⟨W, hW, rfl⟩
    have hZ : A.symm W ∈ H.carrier :=
      (rescalingStable_carrier_iff hCoordinates hM12 hM13 G Q hQ a E E' H H' _).mpr
        (by simpa only [A, ContinuousLinearEquiv.apply_symm_apply] using hW)
    refine ⟨H.endpoint_slice_map (A.symm W), ⟨A.symm W, hZ, rfl⟩, ?_⟩
    simpa only [A, ContinuousLinearEquiv.apply_symm_apply] using
      rescalingStableEndpoint hCoordinates hM12 hM13 G Q hQ a E E' H H' (A.symm W) hZ

include hCoordinates in

theorem rescalingStableImage_values {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E') :
    (fun q => q.val) '' (H.endpoint_slice_map '' H.carrier) =
      (fun q => q.val) '' (H'.endpoint_slice_map '' H'.carrier) := by
  rw [← rescalingStableImage hCoordinates hM12 hM13 G Q hQ a E E' H H']
  simp only [image_image]
  exact image_congr (fun Z _ => (rescalingSliceAt_val hM12 hM13 G Q hQ a
    (T - τ) (parabolicTime Q a T - Q * τ) (rescalingBackwardTime Q a T τ)
      (H.endpoint_slice_map Z)).symm)

include hCoordinates in

theorem rescalingStableDensityIntegral {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E') :
    (∫ q in H.endpoint_slice_map '' H.carrier, rescalingDensity G T τ x q.val
      ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) =
      ∫ q in H'.endpoint_slice_map '' H'.carrier,
        rescalingDensity (rescalingTransport hM12 hM13 G Q hQ a)
          (parabolicTime Q a T) (Q * τ) x q.val
          ∂calibratedMetricVolume
            ((rescalingTransport hM12 hM13 G Q hQ a).slices
              (parabolicTime Q a T - Q * τ)).metricOnPoints := by
  let f := rescalingSliceAt hM12 hM13 G Q hQ a (T - τ) (parabolicTime Q a T - Q * τ)
    (rescalingBackwardTime Q a T τ)
  rw [← rescalingStableImage hCoordinates hM12 hM13 G Q hQ a E E' H H',
    rescalingSliceAt_setIntegral hM12 hM13 G Q hQ a]
  have heq : EqOn (fun p : (G.slices (T - τ)).Point =>
      rescalingDensity (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * τ) x (f p).val)
      (fun p => Real.rpow Q (-(n : ℝ) / 2) * rescalingDensity G T τ x p.val)
      (H.endpoint_slice_map '' H.carrier) := by
    rintro q ⟨Z, hZ, rfl⟩
    have hfval := rescalingSliceAt_val hM12 hM13 G Q hQ a _ _
      (rescalingBackwardTime Q a T τ) (H.endpoint_slice_map Z)
    change (f (H.endpoint_slice_map Z)).val = (H.endpoint_slice_map Z).val at hfval
    dsimp only
    rw [hfval]
    obtain ⟨p, _, hp, _⟩ := H.minimizing_path Z hZ
    have hfinite := finiteValueDomain_of_minimizing p hp
    rw [H.endpoint_slice_map_val Z hZ]
    exact rescalingDensity_scale hM12 hM13 G Q hQ a H.tau_pos hfinite
  rw [setIntegral_congr_fun (by
    obtain ⟨D⟩ := measureJacobianData H
    exact D.image_measurable) heq]
  rw [integral_const_mul, ← mul_assoc]
  have hcancel : Real.rpow Q ((n : ℝ) / 2) * Real.rpow Q (-(n : ℝ) / 2) = 1 := by
    change Q ^ ((n : ℝ) / 2) * Q ^ (-(n : ℝ) / 2) = 1
    rw [← Real.rpow_add hQ]
    have hsum : (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 := by ring
    rw [hsum, Real.rpow_zero]
  rw [hcancel, one_mul]

end PoincareConjecture.M14
