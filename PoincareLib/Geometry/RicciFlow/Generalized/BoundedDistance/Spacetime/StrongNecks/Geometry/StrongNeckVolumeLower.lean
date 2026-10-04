import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckVolumeImages
import PoincareLib.Geometry.Riemannian.Comparison.Volume.CenterDensity

/-!
# Actual uniform local noncollapse in a normalized source neck

The universal positive coefficient comes from a Euclidean coordinate ball
captured in the actual metric ball and the retained Jacobian lower bound.
The containing radius may grow with the neck length; every local radius
up to one eighth is allowed. Source: Morgan--Tian Theorem 5.6, pp. 85-87,
and Claims 10.7-10.10; see the normalized-neck-volume derivation.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

open tube RiemannianMetric

private abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The fixed Euclidean-volume coefficient in normalized source-neck
noncollapse, chosen before every source manifold and local radius. -/
def normalizedNeckVolumeLowerConstant : ℝ :=
  euclideanUnitBallVolume 3 / (48 * 4 ^ 3)

/-- The fixed local-volume coefficient is strictly positive. -/
theorem normalizedNeckVolumeLowerConstant_pos :
    0 < normalizedNeckVolumeLowerConstant :=
  div_pos (euclideanUnitBallVolume_pos 3) (by norm_num)

variable {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

/-- Every small metric ball centered in the variable buffered center ball
has a uniform positive volume lower bound, derived from the actual
normalized neck. No noncollapse hypothesis is supplied. -/
theorem normalized_neck_ball_volume_lower (N : EpsilonNeck g)
    (hscale : N.scale = 1) (hcarrier : N.carrier = univ)
    (hsmall : N.epsilon ≤ (1 / 200 : ℝ)) {S : ℝ} (hSpos : 0 < S)
    (hS : S ≤ N.epsilon⁻¹ / 16) {q : M} (hq : q ∈ g.ball N.center S)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) :
    ENNReal.ofReal (normalizedNeckVolumeLowerConstant * δ ^ 3) ≤
      g.volumeMeasure (g.ball q δ) := by
  let z := N.coordinate_inverse q
  have hs : |z.2| ≤ 2 * S :=
    (normalized_neck_height_lt_of_mem_ball N hscale hcarrier hSpos hq).le
  have hunit : Metric.ball (0 : E) (δ / 4) ⊆ Metric.closedBall 0 1 := by
    intro x hx
    have hxnorm : ‖x‖ < δ / 4 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hvolume := (normalized_neck_chart_image_volume_bounds N hscale hsmall hS
    z.1 hs measurableSet_ball hunit).1
  have hidentity : ENNReal.ofReal (1 / 48 : ℝ) *
      volume (Metric.ball (0 : E) (δ / 4)) =
        ENNReal.ofReal (normalizedNeckVolumeLowerConstant * δ ^ 3) := by
    rw [euclidean_ball_volume_eq 3 (div_pos hδ (by norm_num)),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 48)]
    congr 1
    unfold normalizedNeckVolumeLowerConstant
    ring
  rw [hidentity] at hvolume
  have hcenter : cylinderNeckChart N z.1 z.2 0 = q := by
    rw [cylinderNeckChart_zero]
    exact N.coordinate_map_coordinate_inverse (by rw [hcarrier]; exact mem_univ _)
  have hcapture := normalized_neck_chart_ball_subset N hscale hsmall hS z.1 hs hδ hδsmall
  rw [hcenter] at hcapture
  exact hvolume.trans (measure_mono hcapture)

end PoincareMT.M28
