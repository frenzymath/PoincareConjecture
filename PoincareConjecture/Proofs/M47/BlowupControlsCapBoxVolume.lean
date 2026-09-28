import PoincareConjecture.Proofs.M47.BlowupControlsCapBoxBall
import PoincareConjecture.Proofs.M34.Standard.LocalCalibratedImageVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Euclidean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M}

theorem cap_neck_small_ball_volume (N : EpsilonNeck g) (q : UnitTwoSphere) {z r : ℝ}
    (hz : -N.epsilon⁻¹ < z) (hright : z + 1 < N.epsilon⁻¹)
    (hr : 0 < r) (hrscale : r ≤ 2 * N.scale) :
    ENNReal.ofReal (r ^ 3 / 432) ≤
      calibratedMetricVolume g (g.ball (N.coordinate_map (q, z)) r) := by
  have hscale := N.scale_pos
  let a := r / (6 * N.scale)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haSmall : a ≤ 1 / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 6 * N.scale)).mpr
    linarith
  let e := capBoxChart N q z
  have hsource : capHalfBox a ⊆ e.source := by
    intro p hp
    exact capHalfBox_segment_subset N hz hright ha haSmall hp (right_mem_segment ℝ 0 p)
  have hC : 0 < 2 / N.scale := by positivity
  have hvolume := M34.calibratedMetricVolume_le_mul_image_of_local_tangentNorm_lower
    (RiemannianMetric.euclideanMetric 3) g e.toOpenPartialHomeomorph
    (e.contMDiffOn_toFun.of_le (by simp))
    (e.contMDiffOn_invFun.of_le (by simp)) hC
    (fun p hp v => by
      rw [RiemannianMetric.euclideanMetric_tangentNorm]
      exact capBoxChart_inverse_tangent_bound N q z hp v)
    (capHalfBox_isOpen a).measurableSet hsource
  rw [capHalfBox_volume ha] at hvolume
  have hefun : (e.toOpenPartialHomeomorph : E → M) = (e : E → M) := rfl
  rw [hefun] at hvolume
  have hC3 : 0 < (2 / N.scale) ^ 3 := by positivity
  have hquotient : (4 * a ^ 3) / (2 / N.scale) ^ 3 = r ^ 3 / 432 := by
    dsimp [a]
    field_simp
    ring
  calc
    ENNReal.ofReal (r ^ 3 / 432) =
        ENNReal.ofReal (4 * a ^ 3) / ENNReal.ofReal ((2 / N.scale) ^ 3) := by
      rw [← ENNReal.ofReal_div_of_pos hC3, hquotient]
    _ ≤ calibratedMetricVolume g (e '' capHalfBox a) := by
      apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hC3).ne'
        ENNReal.ofReal_ne_top).mpr
      rw [ENNReal.ofReal_pow hC.le]
      simpa only [mul_comm] using hvolume
    _ ≤ calibratedMetricVolume g (g.ball (N.coordinate_map (q, z)) r) :=
      measure_mono (capHalfBox_image_subset_ball N q hz hright hr hrscale)

end PoincareConjecture.M47
