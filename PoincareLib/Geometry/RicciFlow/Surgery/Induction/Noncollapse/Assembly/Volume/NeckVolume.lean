import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.NeckPatch

/-!
# Tested-ball volume in a canonical neck

Morgan--Tian Proposition 16.3, p. 368. The shared neck image-volume theorem
and actual cylinder product measure turn the contained coordinate patch
into a scale-independent cubic lower bound.
-/

set_option autoImplicit false
-- The sphere measure and fixed cylinder rechart retain the same metric data.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.Proofs.M46

/-- The numerical neck constant is fixed before the flow or surgery radius. -/
noncomputable def canonicalNeckVolumeFloor : ℝ := canonicalSphereVolumeFloor / 256

/-- The neck constant is strictly positive. -/
theorem canonicalNeckVolumeFloor_pos : 0 < canonicalNeckVolumeFloor :=
  div_pos canonicalSphereVolumeFloor_pos (by norm_num)

/-- The product patch is measurable for the actual cylinder measure. -/
theorem canonicalNeckPatch_measurable (q : UnitTwoSphere) (a : ℝ) :
    MeasurableSet (canonicalNeckPatch q a) := by
  have hball : MeasurableSet (canonicalSphereMetric.ball q a) := by
    change MeasurableSet {y : UnitTwoSphere |
      canonicalSphereMetric.edist q y < ENNReal.ofReal a}
    simp_rw [canonicalSphereMetric, rescaledMetric_edist,
      Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_edist_eq_angle
        (by norm_num : 1 ≤ (2 : ℕ))]
    apply IsOpen.measurableSet
    apply isOpen_lt _ continuous_const
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (ENNReal.continuous_ofReal.comp (by fun_prop))
  exact hball.prod measurableSet_Ioo

/-- The frozen round-cylinder measure supplies the patch's cubic volume. -/
theorem canonicalNeckPatch_model_volume (q : UnitTwoSphere) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ENNReal.ofReal (canonicalSphereVolumeFloor * a ^ 2 * (2 * a)) ≤
      roundCylinderVolumeMeasure (canonicalNeckPatch q a) := by
  rw [canonicalNeckPatch, roundCylinderVolumeMeasure_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, sub_neg_eq_add]
  rw [ENNReal.ofReal_mul (mul_nonneg canonicalSphereVolumeFloor_pos.le (sq_nonneg a))]
  simpa only [two_mul] using
    mul_le_mul' (canonicalSphere_small_ball_volume q ha ha1) (le_refl (ENNReal.ofReal (2 * a)))

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- The actual neck ball contains the image of a positive-volume patch. -/
theorem canonicalNeck_patch_ball_volume (q : UnitTwoSphere)
    (hq : N.coordinate_map (q, 0) = N.center) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ENNReal.ofReal (N.scale ^ 3 * canonicalSphereVolumeFloor * a ^ 3 / 4) ≤
      g.volumeMeasure (g.ball N.center (4 * N.scale * a)) := by
  have hscale0 := N.scale_pos
  have hroot : 1 / 2 ≤ Real.sqrt (1 - N.epsilon) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half]),
      Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hfactor : ENNReal.ofReal (N.scale / 2) ^ 3 ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 := by
    gcongr
    nlinarith
  have hpatch := N.volumeMeasure_image_bounds (canonicalNeckPatch_measurable q a)
    (canonicalNeckPatch_subset_domain N q ha1)
  have h := (mul_le_mul' hfactor (canonicalNeckPatch_model_volume q ha ha1)).trans
    (hpatch.1.trans (measure_mono (canonicalNeckPatch_image_subset_ball N q hq ha ha1)))
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ N.scale / 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (N.scale / 2) ^ 3)] at h
  have heq : N.scale ^ 3 * canonicalSphereVolumeFloor * a ^ 3 / 4 =
      (N.scale / 2) ^ 3 * (canonicalSphereVolumeFloor * a ^ 2 * (2 * a)) := by ring
  rw [heq]
  exact h

/-- The scale-independent neck estimate used in Proposition 16.3. The
public test's scalar trace will supply the upper bound on s/scale. -/
theorem canonicalNeck_test_ball_volume {s : ℝ} (hs : 0 < s)
    (hscale : s ≤ 3 * N.scale) :
    ENNReal.ofReal (canonicalNeckVolumeFloor * s ^ 3) ≤
      g.volumeMeasure (g.ball N.center s) := by
  have hscale0 := N.scale_pos
  obtain ⟨⟨q, z⟩, ⟨_, hz⟩, hq⟩ := N.central_sphere_eq ▸ N.center_on_central_sphere
  have hz0 : z = 0 := hz
  subst z
  let a := s / (4 * N.scale)
  have ha : 0 < a := div_pos hs (mul_pos (by norm_num) N.scale_pos)
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * N.scale)).mpr
    linarith [N.scale_pos]
  have heq : 4 * N.scale * a = s := by dsimp [a]; field_simp [hscale0.ne']
  have h := canonicalNeck_patch_ball_volume N q hq ha ha1
  rw [heq] at h
  convert h using 1
  congr 1
  unfold canonicalNeckVolumeFloor
  dsimp [a]
  field_simp [hscale0.ne']
  ring

end PoincareMT.Proofs.M46
