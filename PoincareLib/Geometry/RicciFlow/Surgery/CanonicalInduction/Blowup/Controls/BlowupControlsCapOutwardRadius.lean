import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsCapAffineFactor
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsCapBoxVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.NeckCoordinates

/-!
# Actual scalar-normalized radii at added core points

The scalar comparison is evaluated at the actual point, and its value
is bounded by the independently bounded scalar supremum of the actual
ambient ball. Source: Morgan--Tian Definition 9.72(7);
blowup-cap-core-volume.md, K5C.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The sharp scalar comparison gives a coarse explicit floor at every
actual point of the original fine neck. -/
theorem cap_neck_scalar_quarter (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200) {y : M} (hy : y ∈ N.carrier) :
    (1 / 4 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature y := by
  have hz := (N.coordinate_inverse_mem y hy).2
  have h := cap_neck_normalized_scalar_difference N hsmall
    (N.coordinate_inverse y).1 hz
  rw [show N.coordinate_map ((N.coordinate_inverse y).1, (N.coordinate_inverse y).2) = y
    from M36.neck_coordinate_inverse N hy] at h
  have hlo := (abs_le.mp h).1
  linarith

/-- Exact normalized ambient balls at a fine-neck point have radius at
most two actual neck scales. Boundedness is independent of containment. -/
theorem cap_neck_normalized_radius_le (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200) {y : M} (hy : y ∈ N.carrier)
    {r : ℝ} (hr : 0 < r)
    (hbounded : BddAbove (N.connection.scalarCurvature '' g.ball y r))
    (hnormal : scalarCurvatureSupOn g N.connection (g.ball y r) = r⁻¹ ^ 2) :
    r ≤ 2 * N.scale := by
  have hcenter : y ∈ g.ball y r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) y y < ENNReal.ofReal r
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hRle : N.connection.scalarCurvature y ≤ r⁻¹ ^ 2 := by
    rw [← hnormal]
    have h := le_csSup hbounded (mem_image_of_mem N.connection.scalarCurvature hcenter)
    simpa only [scalarCurvatureSupOn, image_eq_range] using h
  have hfloor := cap_neck_scalar_quarter N hsmall hy
  have hmul := mul_le_mul_of_nonneg_left hRle (sq_nonneg N.scale)
  have hnonneg : 0 ≤ N.scale * r⁻¹ := mul_nonneg N.scale_pos.le (inv_nonneg.mpr hr.le)
  have hdiv : (1 / 2 : ℝ) ≤ N.scale / r := by
    have hproduct : (1 / 2 : ℝ) ≤ N.scale * r⁻¹ := by
      apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hnonneg).mp
      nlinarith only [hfloor, hmul]
    simpa only [div_eq_mul_inv] using hproduct
  have h := (le_div_iff₀ hr).mp hdiv
  linarith

variable [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The boundary-neck central sphere receives the same literal numerical
ambient-ball volume bound as an added point of the old end. -/
theorem cap_neck_central_ball_volume (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200) {y : M} (hy : y ∈ N.central_sphere)
    {r : ℝ} (hr : 0 < r) (hrscale : r ≤ 2 * N.scale) :
    ENNReal.ofReal (r ^ 3 / 432) ≤ calibratedMetricVolume g (g.ball y r) := by
  have hcentral := (M36.neck_central_iff N).mp hy
  have hinv : (1200 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos hsmall
    norm_num at h
    exact h
  have hycoord : N.coordinate_map ((N.coordinate_inverse y).1, (0 : ℝ)) = y := by
    rw [← hcentral.2]
    exact M36.neck_coordinate_inverse N hcentral.1
  rw [← hycoord]
  exact cap_neck_small_ball_volume N (N.coordinate_inverse y).1
    (by linarith) (by linarith) hr hrscale

end PoincareMT.M47
