import PoincareConjecture.Proofs.M47.RetainedNeckChart
import PoincareConjecture.Proofs.M47.RetainedNeckDistance
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_NeckVolume
import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

private noncomputable def retainedNeckPatch (q : UnitTwoSphere) (a : ℝ) :
    Set RoundCylinderSpace := M46.canonicalSphereMetric.ball q a ×ˢ Ioo (-a) 0

private theorem retainedNeckPatch_isOpen (q : UnitTwoSphere) (a : ℝ) :
    IsOpen (retainedNeckPatch q a) := by
  have hball : IsOpen (M46.canonicalSphereMetric.ball q a) := by
    change IsOpen {y : UnitTwoSphere |
      M46.canonicalSphereMetric.edist q y < ENNReal.ofReal a}
    simp_rw [M46.canonicalSphereMetric, rescaledMetric_edist,
      Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_edist_eq_angle
        (by norm_num : 1 ≤ (2 : ℕ))]
    apply isOpen_lt _ continuous_const
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (ENNReal.continuous_ofReal.comp (by fun_prop))
  exact hball.prod isOpen_Ioo

private theorem retainedNeckPatch_model_volume (q : UnitTwoSphere) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ENNReal.ofReal (M46.canonicalSphereVolumeFloor * a ^ 2 * a) ≤
      roundCylinderVolumeMeasure (retainedNeckPatch q a) := by
  rw [retainedNeckPatch, roundCylinderVolumeMeasure_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, zero_sub, neg_neg]
  rw [ENNReal.ofReal_mul
    (mul_nonneg M46.canonicalSphereVolumeFloor_pos.le (sq_nonneg a))]
  exact mul_le_mul' (M46.canonicalSphere_small_ball_volume q ha ha1) le_rfl

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {g0 : StandardInitialMetric}
  {K : MetricSurgeryConstants} {I : MetricSurgeryInput K g}

private theorem retainedNeckPatch_subset_domain (N : EpsilonNeck g)
    (q : UnitTwoSphere) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    retainedNeckPatch q a ⊆ N.cylinderDomain := by
  apply (M46.canonicalNeckPatch_subset_domain N q ha1).trans'
  intro z hz
  exact ⟨hz.1, hz.2.1, hz.2.2.trans ha⟩

private theorem retainedNeckPatch_image_retained (N : EpsilonNeck g)
    (q : UnitTwoSphere) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    N.coordinate_map '' retainedNeckPatch q a ⊆ N.region (-N.epsilon⁻¹) 0 := by
  rintro _ ⟨z, hz, rfl⟩
  have hdom := retainedNeckPatch_subset_domain N q ha ha1 hz
  refine ⟨M36.neck_coordinate_mem N z hdom, ?_, ?_⟩
  · rw [M36.neck_inverse_coordinate N z hdom]
    exact hdom.2.1
  · rw [M36.neck_inverse_coordinate N z hdom]
    exact hz.2.2

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

private theorem retainedNeckPatch_image_subset_ball (R : MetricSurgeryResult g0 I)
    (q : UnitTwoSphere) (hq : I.neck.coordinate_map (q, 0) = I.neck.center)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    R.collapse '' (I.neck.coordinate_map '' retainedNeckPatch q a) ⊆
      R.metric.ball (R.collapse I.neck.center) (4 * I.neck.scale * a) := by
  let N := I.neck
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : R.output.carrier → Type _) :=
    ⟨R.metric.toRiemannianMetric⟩
  have hroot : Real.sqrt (1 + N.epsilon) < 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos]),
      Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  let C := N.scale * Real.sqrt (1 + N.epsilon)
  have hC : 0 ≤ C := mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  rintro x ⟨_, ⟨⟨r, z⟩, hz, rfl⟩, rfl⟩
  have hsphere := (retained_central_distance R q r).trans
    (mul_le_mul' (le_refl (ENNReal.ofReal C)) hz.1.le)
  rw [← ENNReal.ofReal_mul hC] at hsphere
  have haxis := retained_axial_distance R r
    (show z ∈ Icc (-1 : ℝ) 0 from ⟨by linarith [hz.2.1], hz.2.2.le⟩)
  have habs : |z| ≤ a := by rw [abs_of_neg hz.2.2]; linarith [hz.2.1]
  have haxis' := haxis.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left habs hC))
  change R.metric.edist (R.collapse N.center) (R.collapse (N.coordinate_map (r, z))) <
    ENNReal.ofReal _
  rw [← hq]
  calc
    _ ≤ R.metric.edist (R.collapse (N.coordinate_map (q, 0)))
          (R.collapse (N.coordinate_map (r, 0))) +
        R.metric.edist (R.collapse (N.coordinate_map (r, 0)))
          (R.collapse (N.coordinate_map (r, z))) := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (C * a) + ENNReal.ofReal (C * a) := add_le_add hsphere haxis'
    _ = ENNReal.ofReal (2 * C * a) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hC ha.le) (mul_nonneg hC ha.le)]
      congr 1
      ring
    _ < ENNReal.ofReal (4 * N.scale * a) := by
      apply (ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) N.scale_pos) ha)).mpr
      have h := mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left hroot N.scale_pos) ha
      dsimp [C]
      nlinarith

variable [SecondCountableTopology M]

private theorem retainedNeck_patch_ball_volume (R : MetricSurgeryResult g0 I)
    (q : UnitTwoSphere) (hq : I.neck.coordinate_map (q, 0) = I.neck.center)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ENNReal.ofReal (I.neck.scale ^ 3 * M46.canonicalSphereVolumeFloor * a ^ 3 / 8) ≤
      calibratedMetricVolume R.metric
        (R.metric.ball (R.collapse I.neck.center) (4 * I.neck.scale * a)) := by
  let N := I.neck
  have hscale0 := N.scale_pos
  have hroot : 1 / 2 ≤ Real.sqrt (1 - N.epsilon) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half]),
      Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hfactor : ENNReal.ofReal (N.scale / 2) ^ 3 ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 := by
    gcongr
    nlinarith [N.scale_pos]
  have hdom := retainedNeckPatch_subset_domain N q ha ha1
  have hopen : IsOpen (N.coordinate_map '' retainedNeckPatch q a) :=
    N.coordinatePartialHomeomorph.isOpen_image_of_subset_source
      (retainedNeckPatch_isOpen q a) hdom
  have hretained := retained_negative_volume_eq R hopen.measurableSet
    (retainedNeckPatch_image_retained N q ha ha1)
  have hpatch := N.volumeMeasure_image_bounds (retainedNeckPatch_isOpen q a).measurableSet hdom
  have h := (mul_le_mul' hfactor (retainedNeckPatch_model_volume q ha ha1)).trans hpatch.1
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ N.scale / 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (N.scale / 2) ^ 3)] at h
  have heq : N.scale ^ 3 * M46.canonicalSphereVolumeFloor * a ^ 3 / 8 =
      (N.scale / 2) ^ 3 * (M46.canonicalSphereVolumeFloor * a ^ 2 * a) := by ring
  rw [heq]
  apply h.trans
  rw [← M15.calibratedMetricVolume_eq_volumeMeasure g, ← hretained]
  exact measure_mono (retainedNeckPatch_image_subset_ball R q hq ha ha1)

theorem retained_neck_ball_volume (R : MetricSurgeryResult g0 I)
    {s : ℝ} (hs : 0 < s) (hscale : s ≤ I.neck.scale) :
    ENNReal.ofReal (M46.canonicalSphereVolumeFloor / 512 * s ^ 3) ≤
      calibratedMetricVolume R.metric (R.metric.ball (R.collapse I.neck.center) s) := by
  let N := I.neck
  have hscale0 := N.scale_pos
  obtain ⟨⟨q, z⟩, ⟨_, hz⟩, hq⟩ := N.central_sphere_eq ▸ N.center_on_central_sphere
  have hz0 : z = 0 := hz
  subst z
  let a := s / (4 * N.scale)
  have ha : 0 < a := div_pos hs (mul_pos (by norm_num) N.scale_pos)
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * N.scale)).mpr
    linarith [N.scale_pos]
  have heq : 4 * N.scale * a = s := by dsimp [a]; field_simp [N.scale_pos.ne']
  have h := retainedNeck_patch_ball_volume R q hq ha ha1
  rw [heq] at h
  convert h using 1
  congr 1
  dsimp [a]
  field_simp [N.scale_pos.ne']
  ring

end PoincareConjecture.Proofs.M47
