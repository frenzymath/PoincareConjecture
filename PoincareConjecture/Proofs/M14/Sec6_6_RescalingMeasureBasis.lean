import PoincareConjecture.Proofs.M14.Sec6_7_MeasureTransport

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

noncomputable def rescalingMeasureDataWithBasis (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) : M14MeasureJacobianData G T τ x E H := by
  classical
  let : T2Space (G.Horizontal x) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let c (Z : G.Horizontal x) (_hZ : Z ∈ H.carrier) :=
    Classical.choose (exists_orthonormal_tangentBasis
      (G.slices (T - τ)).metricOnPoints (H.endpoint_slice_map Z))
  have hc (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) (i j : Fin n) :
      (G.slices (T - τ)).metricOnPoints.inner (H.endpoint_slice_map Z)
        (c Z hZ i) (c Z hZ j) = if i = j then 1 else 0 :=
    Classical.choose_spec (exists_orthonormal_tangentBasis
      (G.slices (T - τ)).metricOnPoints (H.endpoint_slice_map Z)) i j
  let C := b.euclideanCoordinates
  let e := stableCoordinateChart H b
  let ρ := M10.pullbackJacobian (G.slices (T - τ)).metricOnPoints e
  let J : G.Horizontal x → ℝ := fun Z => ρ (C.symm Z)
  have hJ (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) :
      J Z = M14MetricJacobianFromBasis G b c Z hZ := by
    have hpre : b.euclideanCoordinates (C.symm Z) ∈ H.carrier := by
      simpa only [C, ContinuousLinearEquiv.apply_symm_apply] using hZ
    have h := pullbackJacobian_eq_metricJacobian H b c (C.symm Z) hpre
    simpa only [J, ρ, C, e, ContinuousLinearEquiv.apply_symm_apply] using h
  have he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source :=
    (stableCoordinateChart_smooth H b).of_le (by simp)
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target :=
    (stableCoordinateChart_symm_smooth H b).of_le (by simp)
  have hρ : ContinuousOn ρ e.source := by
    intro z hz
    exact (M10.pullbackJacobian_continuousAt (G.slices (T - τ)).metricOnPoints
      (he.contMDiffAt (e.open_source.mem_nhds hz))).continuousWithinAt
  refine {
    sourceMeasure := M14HorizontalCoordinateVolume G b
    sourceBasis := b
    targetBasis := c
    source_basis_orthonormal := hb
    target_basis_orthonormal := hc
    source_volume_eq_metric_volume := rfl
    carrier_measurable := H.carrier_open.measurableSet
    endpoint_measurable := H.endpoint_slice_continuous.domRestrict.measurable
    image_measurable := e.open_target.measurableSet
    jacobian := J
    jacobian_eq := hJ
    coordinate_jacobian_eq := fun Z hZ => (hJ Z hZ).trans
      (metricJacobian_eq_coordinateJacobian b c hc Z hZ)
    jacobian_nonnegative := fun Z => M10.pullbackJacobian_nonneg _ _ _
    change_of_variables := ?_ }
  intro φ hφ
  let f : G.Horizontal x → ℝ := fun Z => φ (H.endpoint_slice_map Z) * J Z
  have hfcomp : f ∘ C = fun z => ρ z * φ (e z) := by
    funext z
    change φ (H.endpoint_slice_map (C z)) * ρ (C.symm (C z)) =
      ρ z * φ (H.endpoint_slice_map (C z))
    rw [ContinuousLinearEquiv.symm_apply_apply, mul_comm]
  have hsource := b.integrableOn_coordinateVolume_iff f H.carrier
  have hsourceIntegral := b.setIntegral_coordinateVolume f H.carrier
  rw [hfcomp] at hsource hsourceIntegral
  have hφae : MeasureTheory.AEStronglyMeasurable φ
      ((calibratedMetricVolume (G.slices (T - τ)).metricOnPoints).restrict e.target) :=
    hφ.aestronglyMeasurable
  have htarget := M10.integrableOn_calibrated_iff_pullback
    (G.slices (T - τ)).metricOnPoints e he hei hρ hφae
  have htargetIntegral := M10.integralOn_calibrated_eq_pullback
    (G.slices (T - τ)).metricOnPoints e he hei hρ hφae
  exact ⟨hsource.trans htarget.symm, hsourceIntegral.trans htargetIntegral.symm⟩

theorem rescalingMeasureDataWithBasis_sourceBasis (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) :
    (rescalingMeasureDataWithBasis H b hb).sourceBasis = b := rfl

end PoincareConjecture.M14
