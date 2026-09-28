import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.SourceLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.LimitLinkRigidity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.VolumeRigidity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem curvature_eq_zero_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 2))) M] [IsManifold (𝓡 (n + 2)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 2) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (n + 2)) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    ∀ x : M, (F.connection t₀).scalarCurvature x = 0 ∧
      (F.connection t₀).curvatureTensorNorm x = 0 := by
  let := (F.metric t₀).toMetricSpace
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hc := (F.metric t₀).rayComparison_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  let := unitSliceChartedSpace hc (n + 1) hcover
  let := unitSlice_isManifold hc (n + 1) hcover
  obtain ⟨f, N, hf, hN, himm, hunit, hderiv, hsep, hmetric⟩ :=
    F.exists_unitSlice_euclidean_umbilic_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  obtain ⟨e⟩ := (F.metric t₀).nonempty_asymptoticLink_chordal_isometry_of_unit_umbilic
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p (by omega : 1 ≤ n + 1)
    hcover f N hf hN himm hunit hderiv hsep hmetric
  have hvolume := asymptoticCone_radial_unit_ball_volume_of_chordal_isometry hc
    (by omega : 1 ≤ n + 2) e
  have hflat := (F.metric t₀).curvatureTensor_eq_zero_of_asymptoticCone_volume_ge_euclidean
    (F.connection t₀) (by omega : 2 ≤ n + 2) (hcomplete t₀ ht₀)
    (hoperator t₀ ht₀) p hvolume.symm.le
  intro x
  constructor
  · simp only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci, hflat,
      Finset.sum_const_zero]
  · simp only [LeviCivitaData.curvatureTensorNorm, hflat, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, Real.sqrt_zero]

end PoincareConjecture.RicciFlow
