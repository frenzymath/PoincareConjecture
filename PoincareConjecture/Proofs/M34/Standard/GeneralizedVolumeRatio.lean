import PoincareConjecture.Proofs.M34.Standard.GeneralizedVolumeTransfer
import PoincareConjecture.Proofs.M34.Mathlib.RescaledVolumeRatio
import PoincareConjecture.Definitions.Ch09.AsymptoticVolume
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.GeneralizedBlowupConvergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold
local instance : MeasurableSpace C.limit.carrier.carrier := C.limit.carrier.measurableSpace
local instance : BorelSpace C.limit.carrier.carrier := C.limit.carrier.borelSpace
local instance : T3Space C.limit.carrier.carrier := C.limit.carrier.t3Space

theorem eventually_source_ball_volume_ratio_le_zero (a : ℝ) (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop,
      calibratedMetricVolume ((S.flow (C.subsequence k)).metric
        (S.base (C.subsequence k)).1) (S.baseBall (C.subsequence k) a) /
          ENNReal.ofReal (a / Real.sqrt (S.scale (C.subsequence k))) ^ 3 ≤
      64 * metricBallVolumeRatio (C.limit.flow.metric 0) C.limit.base
        ⟨2 * a, mul_pos two_pos ha⟩ := by
  filter_upwards [C.eventually_source_ball_volume_le_zero a ha] with k hk
  apply (ENNReal.div_le_div_right hk _).trans_eq
  simpa only [metricBallVolumeRatio, show (2 : ℝ) * 2 = 4 by norm_num,
    ENNReal.ofReal_ofNat, show (4 : ℝ≥0∞) ^ 3 = 64 by norm_num] using
    ENNReal.rescaled_power_volume_ratio
      (calibratedMetricVolume (C.limit.flow.metric 0)
        ((C.limit.flow.metric 0).ball C.limit.base (2 * a))) 3
      (q := Real.sqrt (S.scale (C.subsequence k))) ha
      (Real.sqrt_pos.mpr (S.base_scalar_pos (C.subsequence k)))
      (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) < 2 by norm_num)

end PoincareConjecture.GeneralizedBlowupConvergence
