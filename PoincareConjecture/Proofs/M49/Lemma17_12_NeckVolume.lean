import PoincareConjecture.Proofs.M49.CylinderDensityPatch
import PoincareConjecture.Proofs.M49.CylinderCoordinateBox
import PoincareConjecture.Proofs.M49.NeckChartJacobian
import PoincareConjecture.Proofs.M10.CalibratedTransport

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M49

theorem exists_uniform_positive_half_neck_volume :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T3Space M] [MeasurableSpace M] [BorelSpace M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g), N.epsilon ≤ d →
        ENNReal.ofReal (c * N.scale ^ 3 / N.epsilon) ≤
          calibratedMetricVolume g (N.region 0 N.epsilon⁻¹) := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0,
    by simp⟩
  obtain ⟨r, d, a, hr, hd, ha, hpatch⟩ := exists_cylinder_density_patch q
  refine ⟨a * r ^ 2, d, mul_pos ha (pow_pos hr _), hd, ?_⟩
  intro M _ _ _ _ _ _ g N hsmall
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let e := epsilonNeckEuclideanChart N q
  let A := cylinderCoordinateBox (c q) r N.epsilon⁻¹
  have hA : MeasurableSet A := (isOpen_cylinderCoordinateBox _ _ _).measurableSet
  have hline : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hbox (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ A) :
      (cylinderCoordinateEquiv x).1 ∈ Metric.ball (c q) r ∧
        (cylinderCoordinateEquiv x).2 ∈ Ioo 0 N.epsilon⁻¹ :=
    cylinderCoordinateBox_subset (c q) hr N.epsilon⁻¹ hx
  have hsource : A ⊆ e.source := by
    intro x hx
    rw [epsilonNeckEuclideanChart_source]
    exact ⟨(hpatch _ (hbox x hx).1).1,
      (neg_neg_of_pos hline).trans (hbox x hx).2.1, (hbox x hx).2.2⟩
  have hJ (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ A) :
      N.scale ^ 3 * a ≤ M10.pullbackJacobian g e x := by
    let p := cylinderCoordinateEquiv x
    let Q : Matrix (Fin 3) (Fin 3) ℝ := fun i j => N.scale⁻¹ ^ 2 *
      roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map) c p i j
    have hp : p.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨(neg_neg_of_pos hline).trans (hbox x hx).2.1, (hbox x hx).2.2⟩
    have hdensity : a ≤ Real.sqrt Q.det := (hpatch p (hbox x hx).1).2 Q (by
      intro i j
      exact (epsilonNeck_coefficient_error_le N c p hp i j).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
    rw [epsilonNeckEuclideanChart_jacobian_eq N q x (hsource hx)]
    exact mul_le_mul_of_nonneg_left hdensity (pow_nonneg N.scale_pos.le _)
  have hvolume := M10.calibratedMetricVolume_image_eq_lintegral g e
    ((epsilonNeckEuclideanChart_contMDiffOn N q).of_le (by simp))
    ((epsilonNeckEuclideanChart_symm_contMDiffOn N q).of_le (by simp)) hA hsource
  have himage : e '' A ⊆ N.region 0 N.epsilon⁻¹ := by
    rw [← epsilonNeckChart_image_region N 0 N.epsilon⁻¹
      (neg_nonpos.mpr hline.le) le_rfl]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(c.symm (cylinderCoordinateEquiv x).1, (cylinderCoordinateEquiv x).2),
      ⟨mem_univ _, (hbox x hx).2⟩, rfl⟩
  calc
    ENNReal.ofReal (a * r ^ 2 * N.scale ^ 3 / N.epsilon) =
        ENNReal.ofReal (N.scale ^ 3 * a) * volume A := by
      rw [volume_cylinderCoordinateBox _ hr.le,
        ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg N.scale_pos.le _) ha.le)]
      congr 1
      simp only [div_eq_mul_inv]
      ring
    _ = ∫⁻ _ in A, ENNReal.ofReal (N.scale ^ 3 * a) := by simp
    _ ≤ calibratedMetricVolume g (e '' A) := by
      rw [hvolume]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact ENNReal.ofReal_le_ofReal (hJ x hx)
    _ ≤ calibratedMetricVolume g (N.region 0 N.epsilon⁻¹) := measure_mono himage

end PoincareConjecture.M49
