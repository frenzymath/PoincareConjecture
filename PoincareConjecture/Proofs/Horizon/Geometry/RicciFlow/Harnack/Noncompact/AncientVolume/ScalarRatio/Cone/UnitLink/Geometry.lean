import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Curvature













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow





theorem unitSlice_geometry_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (n + 1)) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hc := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    let gL := unitSliceMetric hcover
    Nonempty (AsymptoticConeUnitSlice p hc) ∧
      CompactSpace (AsymptoticConeUnitSlice p hc) ∧
      SecondCountableTopology (AsymptoticConeUnitSlice p hc) ∧
      IsManifold (𝓡 n) ∞ (AsymptoticConeUnitSlice p hc) ∧
      MetricComplete gL ∧
      (∀ (x : AsymptoticConeUnitSlice p hc) (u v w a : TangentSpace (𝓡 n) x),
        gL.leviCivitaData.curvatureTensor x u v w a =
          gL.inner x u w * gL.inner x v a - gL.inner x u a * gL.inner x v w) ∧
      (∀ (x : AsymptoticConeUnitSlice p hc) (u v : TangentSpace (𝓡 n) x),
        gL.inner x u u * gL.inner x v v - gL.inner x u v ^ 2 ≠ 0 →
        gL.leviCivitaData.sectionalCurvature x u v = 1) := by
  let := (F.metric t₀).toMetricSpace
  let := (F.metric t₀).properSpace_toMetricSpace (hcomplete t₀ ht₀)
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hc := (F.metric t₀).rayComparison_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  have hmetricComplete : MetricComplete (unitSliceMetric hcover) := by
    dsimp only [MetricComplete]
    infer_instance
  exact ⟨nonempty_asymptoticConeUnitSlice hc
    ((F.metric t₀).nonempty_basedMinimizingRays (hcomplete t₀ ht₀) p),
    inferInstance, inferInstance, inferInstance, hmetricComplete,
    unitSliceMetric_curvatureTensor_eq_one hcover, unitSliceMetric_sectionalCurvature_eq_one hcover⟩

end PoincareConjecture.RicciFlow
