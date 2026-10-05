import PoincareLib.Geometry.Spacetime.Rescaling.Atlas
import PoincareLib.Geometry.Spacetime.Rescaling.Interval
import PoincareLib.Geometry.Riemannian.Homothety.Basic
import PoincareLib.Geometry.Spacetime.GeometryTheory

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M13SpacetimeRescaling.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Constructed parabolic spacetime geometry

Morgan-Tian Definition 3.40, p. 61. The target is an actual realization of
the rescaled atlas on the same chosen smooth carrier. Horizontal transport
is the identity on underlying tangent vectors, not an arbitrary fiber map.
Slice identifications include every real time and hence the empty slices
outside the exact time image. M13 supplies existence of this entire record.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X}

/-- The actual rescaled realization, with its clock, kernels and slice maps. -/
structure ParabolicSpacetimeRescaling (R : GeneralizedFlowCarrierConclusion A)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) where
  atlasRescaling : ParabolicAtlasRescaling A Q hQ a
  realization : GeneralizedFlowCarrierConclusion atlasRescaling.atlas
  intervalSystem_eq : realization.timeIntervals = R.timeIntervals
  intervalTransport : ParabolicIntervalTransport R.timeIntervals Q hQ a
  chartedSpace_eq : realization.spacetime.chartedSpace = R.spacetime.chartedSpace
  identification : Diffeomorph (spacetimeModel n) (spacetimeModel n)
    R.spacetime.Point realization.spacetime.Point ∞
  identification_eq : ∀ p : R.spacetime.Point, identification p = p
  differential_eq : ∀ (p : R.spacetime.Point)
    (Z : TangentSpace (spacetimeModel n) p),
    (show SpacetimeModelVector n from
      mfderiv (spacetimeModel n) (spacetimeModel n) identification p Z) = Z
  time_differential : ∀ (p : R.spacetime.Point)
    (Z : TangentSpace (spacetimeModel n) p),
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      realization.spacetime.timeFunction p Z) =
      Q * (show ℝ from
        mfderiv (spacetimeModel n) 𝓘(ℝ) R.spacetime.timeFunction p Z)
  timeVector_eq : ∀ p : R.spacetime.Point,
    (show SpacetimeModelVector n from realization.spacetime.timeVector p) =
      (1 / Q : ℝ) • R.spacetime.timeVector p
  horizontal : ∀ p : R.spacetime.Point,
    R.spacetime.Horizontal p ≃L[ℝ] realization.spacetime.Horizontal p
  horizontal_val : ∀ (p : R.spacetime.Point) (v : R.spacetime.Horizontal p),
    (show SpacetimeModelVector n from (horizontal p v).val) = v.val
  horizontal_smooth :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) R.spacetime.Horizontal ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := realization.spacetime.Horizontal) v.proj (horizontal v.proj v.2))
  horizontal_inverse_smooth :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
          realization.spacetime.Horizontal ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := R.spacetime.Horizontal) v.proj ((horizontal v.proj).symm v.2))
  projection_eq : ∀ (p : R.spacetime.Point)
    (Z : TangentSpace (spacetimeModel n) p),
    realization.spacetime.horizontalProjection p Z =
      horizontal p (R.spacetime.horizontalProjection p Z)
  metric_eq : ∀ (p : R.spacetime.Point) (v w : R.spacetime.Horizontal p),
    realization.spacetime.horizontalMetric.inner p (horizontal p v) (horizontal p w) =
      Q * R.spacetime.horizontalMetric.inner p v w
  sliceIdentification : ∀ t : ℝ,
    Diffeomorph (𝓡 n) (𝓡 n) (R.slices t).Point
      (realization.slices (parabolicTime Q a t)).Point ∞
  sliceIdentification_eq : ∀ (t : ℝ) (x : (R.slices t).Point),
    (sliceIdentification t x).val = x.val
  slice_tangent : ∀ (t : ℝ) (x : (R.slices t).Point)
    (v : TangentSpace (𝓡 n) x),
    (show SpacetimeModelVector n from
      ((realization.slices (parabolicTime Q a t)).tangentEquiv
        (sliceIdentification t x)
        (mfderiv (𝓡 n) (𝓡 n) (sliceIdentification t) x v)).val) =
      (horizontal x.val ((R.slices t).tangentEquiv x v)).val
  slice_metric : ∀ t : ℝ,
    MetricHomothety (R.slices t).metricOnPoints
      (realization.slices (parabolicTime Q a t)).metricOnPoints
      (sliceIdentification t) Q

end PoincareMT
