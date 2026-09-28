import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.FlatMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.CenterDensity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem volumeMeasure_ball_injectivityRadius_eq_euclidean_of_flat
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hflat : ∀ x : M, D.curvatureTensorNorm x = 0)
    (p : M) {ν : ℝ} (hν : 0 < ν)
    (hvolume : ENNReal.ofReal ν ≤ g.volumeMeasure (g.ball p 1)) :
    let ρ := localInjectivityRadius 3 0 1 ν
    g.volumeMeasure (g.ball p ρ) = ENNReal.ofReal (euclideanUnitBallVolume 3 * ρ ^ 3) := by
  classical
  let ρ := localInjectivityRadius 3 0 1 ν
  have hρ : 0 < ρ := localInjectivityRadius_pos 3 0 (by norm_num) ν
  have hρ1 : ρ < 1 := localInjectivityRadius_lt 3 0 (by norm_num) ν
  obtain ⟨L, e, hL, he, he0, hed, hgeo, _, hinj⟩ :=
    g.exists_precompact_exponential_injective_of_noncollapse D p
      (by norm_num : 1 ≤ 3) (le_refl 0) (by norm_num : (0 : ℝ) < 1) hν
      (g.isCompact_closure_ball_of_metricComplete hc p (2 * 1))
      (fun x _ => (hflat x).le) hvolume
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simp))) he0 hed hL
  have hmetric (v : EuclideanSpace ℝ (Fin 3)) (hv : v ∈ Metric.ball 0 1) :
      g.pullbackCoefficients e v = innerSL ℝ :=
    g.pullbackCoefficients_eq_innerSL_of_flat_radial D he hnorm
      (fun w hw => (hgeo w hw).1) hv (fun t _ => hflat _)
      (fun t ht => ((hgeo v hv).2 t ht).1)
  have hcover := Poincare.VolumeComparison.image_localMinimizingSet_eq_ball
    g p (by norm_num : (0 : ℝ) < 1)
    (g.isCompact_closure_ball_of_metricComplete hc p 1) L e hL he0 hed
    (fun w hw => (hgeo w hw).1)
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball hρ1.le
  have hinj' : InjOn e (Metric.ball 0 ρ) := hinj.mono Metric.ball_subset_closedBall
  have himage := (g.image_ball_and_radial_edist_eq_of_injOn p hρ hρ1.le hcover
    (fun v hv => by simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
      ((hgeo v (hsub hv)).2 1 (by simp)).2) hinj').1
  have hdensity (v : EuclideanSpace ℝ (Fin 3)) (hv : v ∈ Metric.ball 0 ρ) :
      g.pullbackVolumeDensity e v = 1 := by
    have hmatrix : Matrix.of (fun i j : Fin 3 => g.inner (e v)
        (mfderiv (𝓡 3) (𝓡 3) e v (EuclideanSpace.basisFun (Fin 3) ℝ i))
        (mfderiv (𝓡 3) (𝓡 3) e v (EuclideanSpace.basisFun (Fin 3) ℝ j))) = 1 := by
      ext i j
      change g.pullbackCoefficients e v (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) = _
      rw [hmetric v (hsub hv)]
      change inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      rw [EuclideanSpace.basisFun_inner]
      simp [EuclideanSpace.basisFun_apply, Matrix.one_apply]
    simp only [pullbackVolumeDensity, hmatrix, Matrix.det_one, Real.sqrt_one]
  change g.volumeMeasure (g.ball p ρ) = _
  rw [← himage, g.volumeMeasure_image_eq_lintegral_of_mdifferentiableAt_injOn
    Metric.isOpen_ball.measurableSet
    (fun v hv => (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hv))).mdifferentiableAt
      (by simp)) hinj']
  calc
    _ = ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ, (1 : ℝ≥0∞) :=
      setLIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun v hv => by
        rw [hdensity v hv, ENNReal.ofReal_one])
    _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ) := by simp
    _ = _ := euclidean_ball_volume_eq 3 hρ

theorem volumeMeasure_ball_eq_euclidean_of_flat_of_volume_lower_bound
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hflat : ∀ x : M, D.curvatureTensorNorm x = 0)
    (p : M) {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ r : ℝ, 0 < r → ENNReal.ofReal (ν * r ^ 3) ≤
      g.volumeMeasure (g.ball p r)) :
    ∀ r : ℝ, 0 < r →
      g.volumeMeasure (g.ball p r) = ENNReal.ofReal (euclideanUnitBallVolume 3 * r ^ 3) := by
  intro r hr
  let ρ := localInjectivityRadius 3 0 1 ν
  have hρ : 0 < ρ := localInjectivityRadius_pos 3 0 (by norm_num) ν
  let a := ρ / r
  have ha : 0 < a := div_pos hρ hr
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  let g' := rescaledMetric g (a ^ 2) ha2
  let D' := rescaledMetric_connection g D (a ^ 2) ha2
  have hsqrt : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha.le
  have hc' : MetricComplete g' := metricComplete_rescaledMetric g _ ha2 hc
  have hflat' (x : M) : D'.curvatureTensorNorm x = 0 := by
    have hzero (u v w z : TangentSpace (𝓡 3) x) : D.curvatureTensor x u v w z = 0 := by
      have h := ManifoldJacobi.curvature_norm_le D x u v z
      rw [hflat x] at h
      have hz : D.curvature x u v z = 0 := by
        by_contra hne
        have hpos : 0 < g.tangentNorm x (D.curvature x u v z) :=
          Real.sqrt_pos.mpr (g.pos x _ hne)
        exact (not_lt_of_ge (by simpa only [zero_mul] using h)) hpos
      simp only [LeviCivitaData.curvatureTensor, hz, map_zero, zero_apply]
    simp only [D', LeviCivitaData.curvatureTensorNorm, rescaledMetric_curvatureTensor,
      hzero, mul_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, Real.sqrt_zero]
  have hunit : ENNReal.ofReal ν ≤ g'.volumeMeasure (g'.ball p 1) := by
    have h := mul_le_mul_right (hvolume (1 / a) (by positivity)) (ENNReal.ofReal a ^ 3)
    have hid : ENNReal.ofReal a ^ 3 * ENNReal.ofReal (ν * (1 / a) ^ 3) =
        ENNReal.ofReal ν := by
      rw [← ENNReal.ofReal_pow ha.le, ← ENNReal.ofReal_mul (pow_nonneg ha.le 3)]
      congr 1
      field_simp
    rw [hid] at h
    simpa only [g', rescaledMetric_ball, rescaledMetric_volumeMeasure,
      Measure.smul_apply, smul_eq_mul, hsqrt] using h
  have hlocal := g'.volumeMeasure_ball_injectivityRadius_eq_euclidean_of_flat
    D' hc' hflat' p hν hunit
  change g'.volumeMeasure (g'.ball p ρ) = ENNReal.ofReal (euclideanUnitBallVolume 3 * ρ ^ 3)
    at hlocal
  have hrad : ρ / a = r := by dsimp [a]; field_simp
  simp only [g', rescaledMetric_ball, rescaledMetric_volumeMeasure, Measure.smul_apply,
    smul_eq_mul, hsqrt, hrad] at hlocal
  have hid : ENNReal.ofReal (euclideanUnitBallVolume 3 * ρ ^ 3) =
      ENNReal.ofReal a ^ 3 * ENNReal.ofReal (euclideanUnitBallVolume 3 * r ^ 3) := by
    rw [← ENNReal.ofReal_pow ha.le, ← ENNReal.ofReal_mul (pow_nonneg ha.le 3)]
    congr 1
    dsimp [a]
    field_simp
  have h0 : ENNReal.ofReal a ^ 3 ≠ 0 := pow_ne_zero 3 (ENNReal.ofReal_pos.mpr ha).ne'
  have ht : ENNReal.ofReal a ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hcancel := congrArg (fun z : ℝ≥0∞ => (ENNReal.ofReal a ^ 3)⁻¹ * z)
    (hlocal.trans hid)
  simpa only [ENNReal.inv_mul_cancel_left h0 ht] using hcancel

theorem false_of_flat_of_volume_lower_bound_of_half_euclidean_unit_volume
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hflat : ∀ x : M, D.curvatureTensorNorm x = 0)
    (p : M) {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ r : ℝ, 0 < r → ENNReal.ofReal (ν * r ^ 3) ≤
      calibratedMetricVolume g (g.ball p r))
    (hhalf : calibratedMetricVolume g (g.ball p 1) =
      ENNReal.ofReal (euclideanUnitBallVolume 3 / 2)) : False := by
  simp only [calibratedMetricVolume_eq_volumeMeasure] at hvolume hhalf
  have hunit := g.volumeMeasure_ball_eq_euclidean_of_flat_of_volume_lower_bound
    D hc hflat p hν hvolume 1 (by norm_num)
  rw [one_pow, mul_one] at hunit
  have h := (ENNReal.ofReal_eq_ofReal_iff
    (euclideanUnitBallVolume_nonneg 3)
    (div_nonneg (euclideanUnitBallVolume_nonneg 3) (by norm_num))).mp (hunit.symm.trans hhalf)
  linarith [euclideanUnitBallVolume_pos 3]

end PoincareConjecture.RiemannianMetric
