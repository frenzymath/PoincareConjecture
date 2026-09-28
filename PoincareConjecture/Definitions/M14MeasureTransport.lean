import PoincareConjecture.Definitions.M14Exponential
import PoincareConjecture.Definitions.Ch06.ReducedVolume
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

noncomputable instance m14HorizontalMeasurableSpace
    (G : GeneralizedLGeometryTransport n X time I) (x : G.Point) :
    MeasurableSpace (G.Horizontal x) := borel (G.Horizontal x)

instance m14HorizontalBorelSpace
    (G : GeneralizedLGeometryTransport n X time I) (x : G.Point) :
    BorelSpace (G.Horizontal x) := ⟨rfl⟩

noncomputable def M14EndpointTangentDifferential
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
    {H : M14StableSet G T τ x E}
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) :
    G.Horizontal x →L[ℝ]
      TangentSpace (𝓡 n) (H.endpoint_slice_map Z) :=
  (((G.slices (T - τ)).tangentEquiv (H.endpoint_slice_map Z)).symm :
      G.Horizontal (H.endpoint_slice_map Z).val →L[ℝ]
        TangentSpace (𝓡 n) (H.endpoint_slice_map Z)).comp
    ((H.endpoint_slice_map_val Z hZ).symm ▸ H.endpoint_differential Z hZ)

noncomputable def M14MetricJacobianFromBasis
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
    {H : M14StableSet G T τ x E}
    (sourceBasis : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (_targetBasis : ∀ Z : G.Horizontal x, Z ∈ H.carrier →
      Module.Basis (Fin n) ℝ
        (TangentSpace (𝓡 n) (H.endpoint_slice_map Z)))
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) : ℝ :=
  Real.sqrt (max 0 (Matrix.det (fun i j : Fin n =>
    (G.slices (T - τ)).metricOnPoints.inner (H.endpoint_slice_map Z)
      ((M14EndpointTangentDifferential G Z hZ) (sourceBasis i))
      ((M14EndpointTangentDifferential G Z hZ) (sourceBasis j)))))

noncomputable def M14CoordinateJacobianFromBasis
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
    {H : M14StableSet G T τ x E}
    (sourceBasis : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (targetBasis : ∀ Z : G.Horizontal x, Z ∈ H.carrier →
      Module.Basis (Fin n) ℝ
        (TangentSpace (𝓡 n) (H.endpoint_slice_map Z)))
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) : ℝ :=
  |Matrix.det (LinearMap.toMatrix sourceBasis (targetBasis Z hZ)
      (M14EndpointTangentDifferential G Z hZ).toLinearMap)|

noncomputable def M14HorizontalCoordinateVolume
    (G : GeneralizedLGeometryTransport n X time I)
    {x : G.Point}
    (sourceBasis : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    MeasureTheory.Measure (G.Horizontal x) :=
  MeasureTheory.Measure.map (sourceBasis.equivFun).symm MeasureTheory.volume

structure M14MeasureJacobianData
    (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) where
  sourceMeasure : MeasureTheory.Measure (G.Horizontal x)
  sourceBasis : Module.Basis (Fin n) ℝ (G.Horizontal x)
  targetBasis : ∀ Z : G.Horizontal x, Z ∈ H.carrier →
    Module.Basis (Fin n) ℝ
      (TangentSpace (𝓡 n) (H.endpoint_slice_map Z))
  source_basis_orthonormal : ∀ i j,
    G.spacetime.horizontalMetric.inner x (sourceBasis i) (sourceBasis j) =
      if i = j then 1 else 0
  target_basis_orthonormal : ∀ Z hZ i j,
    (G.slices (T - τ)).metricOnPoints.inner (H.endpoint_slice_map Z)
      (targetBasis Z hZ i) (targetBasis Z hZ j) =
      if i = j then 1 else 0
  source_volume_eq_metric_volume :
    sourceMeasure = M14HorizontalCoordinateVolume G sourceBasis
  carrier_measurable : MeasurableSet H.carrier
  endpoint_measurable : Measurable
    (fun Z : H.carrier => H.endpoint_slice_map Z.val)
  image_measurable : MeasurableSet (H.endpoint_slice_map '' H.carrier)
  jacobian : G.Horizontal x → ℝ
  jacobian_eq : ∀ Z hZ,
    jacobian Z = M14MetricJacobianFromBasis G sourceBasis targetBasis Z hZ
  coordinate_jacobian_eq : ∀ Z hZ,
    jacobian Z = M14CoordinateJacobianFromBasis G sourceBasis targetBasis Z hZ
  jacobian_nonnegative : ∀ Z, 0 ≤ jacobian Z
  change_of_variables : ∀ φ : (G.slices (T - τ)).Point → ℝ,
    Measurable φ →
    (MeasureTheory.IntegrableOn
      (fun Z => φ (H.endpoint_slice_map Z) * jacobian Z) H.carrier
        sourceMeasure ↔
      MeasureTheory.IntegrableOn φ (H.endpoint_slice_map '' H.carrier)
        (calibratedMetricVolume (G.slices (T - τ)).metricOnPoints)) ∧
    (∫ Z in H.carrier, φ (H.endpoint_slice_map Z) * jacobian Z ∂sourceMeasure) =
      (∫ q in H.endpoint_slice_map '' H.carrier, φ q
        ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints)

end PoincareConjecture
