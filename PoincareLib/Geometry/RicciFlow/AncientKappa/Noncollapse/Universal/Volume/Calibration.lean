import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.Preparations
import PoincareLib.Geometry.RicciFlow.AncientKappa.Volume.Basic
import PoincareLib.Geometry.Riemannian.Measure.Balls
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Calibrated zero-volume limits

Vanishing of the real normalized ball volumes implies vanishing of the
positive-radius infimum in the frozen ancient-solution volume convention.

Reference: Morgan--Tian, Section 9.6 and Theorem 9.59, pp. 222--225.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- Finite ball volumes let real normalized-volume decay detect the calibrated
positive-radius infimum exactly. -/
theorem calibrated_asymptoticVolumeRatio_eq_zero_of_tendsto (g : RiemannianMetric n M)
    (p : M)
    (hfinite : ∀ r : ℝ, 0 < r → g.volumeMeasure (g.ball p r) ≠ ⊤)
    (hlimit : Tendsto (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)
      atTop (𝓝 0)) :
    PoincareMT.asymptoticVolumeRatio g p = 0 := by
  unfold PoincareMT.asymptoticVolumeRatio metricBallVolumeRatio
  apply le_antisymm _ bot_le
  have hlimit' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlimit
  simp only [ENNReal.ofReal_zero] at hlimit'
  apply ge_of_tendsto hlimit'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hratio : calibratedMetricVolume g (g.ball p r) / ENNReal.ofReal r ^ n =
      ENNReal.ofReal ((g.volumeMeasure (g.ball p r)).toReal / r ^ n) := by
    rw [calibratedMetricVolume_eq_volumeMeasure, ENNReal.ofReal_div_of_pos (pow_pos hr n),
      ENNReal.ofReal_pow hr.le, ENNReal.ofReal_toReal (hfinite r hr)]
  simp only [Function.comp_apply]
  rw [← hratio]
  apply sInf_le
  exact ⟨⟨r, hr⟩, rfl⟩

end PoincareMT.RiemannianMetric
