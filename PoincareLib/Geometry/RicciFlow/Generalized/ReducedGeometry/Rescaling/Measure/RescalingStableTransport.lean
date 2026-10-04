import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Measure.RescalingJacobian
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Measure.RescalingStableVolume

/-!
# Complete stable-carrier analytic transport under rescaling

Morgan-Tian Corollary 6.74 and Lemma 6.75, p. 142. The full stable
record, its exact carrier, actual metric Jacobian, endpoint image and
calibrated density integral are transported together.
-/

set_option autoImplicit false
-- The normalized basis map uses the actual transported horizontal fiber.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

include hCoordinates in
/-- The entire frozen stable-carrier transport clause, with explicit
measure-Jacobian records and the actual calibrated set integral.
Corollary 6.74 and Lemma 6.75, p. 142. -/
theorem rescalingStableTransport {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E) :
    ∃ H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * τ) x E',
      (∀ Z, Z ∈ H.carrier ↔ rescalingInitialEquiv G.spacetime Q hQ a x Z ∈ H'.carrier) ∧
      ∃ D : M14MeasureJacobianData G T τ x E H,
        ∃ D' : M14MeasureJacobianData (rescalingTransport hM12 hM13 G Q hQ a)
            (parabolicTime Q a T) (Q * τ) x E' H',
          (∀ Z, Z ∈ H.carrier → D'.jacobian (rescalingInitialEquiv G.spacetime Q hQ a x Z) =
            Real.rpow Q ((n : ℝ) / 2) * D.jacobian Z) ∧
          (fun q => q.val) '' (H.endpoint_slice_map '' H.carrier) =
            (fun q => q.val) '' (H'.endpoint_slice_map '' H'.carrier) ∧
          (∫ q in H.endpoint_slice_map '' H.carrier, rescalingDensity G T τ x q.val
            ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) =
            ∫ q in H'.endpoint_slice_map '' H'.carrier,
              rescalingDensity (rescalingTransport hM12 hM13 G Q hQ a)
                (parabolicTime Q a T) (Q * τ) x q.val
                ∂calibratedMetricVolume
                  ((rescalingTransport hM12 hM13 G Q hQ a).slices
                    (parabolicTime Q a T - Q * τ)).metricOnPoints := by
  let H' := rescalingStableSet hM12 hM13 G Q hQ a E E' H
  have hcarrier := rescalingStable_carrier_iff hCoordinates hM12 hM13 G Q hQ a E E' H H'
  obtain ⟨D⟩ := measureJacobianData H
  let b' := D.sourceBasis.map (rescalingInitialEquiv G.spacetime Q hQ a x).toLinearEquiv
  have hb' (i j : Fin n) :
      (rescalingTransport hM12 hM13 G Q hQ a).spacetime.horizontalMetric.inner x
        (b' i) (b' j) = if i = j then 1 else 0 := by
    exact (rescalingInitialEquiv_inner G.spacetime Q hQ a x
      (D.sourceBasis i) (D.sourceBasis j)).trans (D.source_basis_orthonormal i j)
  let D' := rescalingMeasureDataWithBasis H' b' hb'
  refine ⟨H', hcarrier, D, D', ?_,
    rescalingStableImage_values hCoordinates hM12 hM13 G Q hQ a E E' H H',
    rescalingStableDensityIntegral hCoordinates hM12 hM13 G Q hQ a E E' H H'⟩
  intro Z hZ
  exact rescalingJacobian_scale hCoordinates hM12 hM13 G Q hQ a E E' H H' D D'
    rfl Z hZ ((hcarrier Z).mp hZ)

end PoincareMT.M14
