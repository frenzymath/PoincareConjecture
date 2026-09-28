import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderVolume
import PoincareConjecture.Proofs.M34.Standard.GeneralizedReverseBall

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

theorem eventually_source_ball_volume_le_zero (a : ℝ) (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop,
      calibratedMetricVolume ((S.flow (C.subsequence k)).metric
        (S.base (C.subsequence k)).1) (S.baseBall (C.subsequence k) a) ≤
      ENNReal.ofReal (2 / Real.sqrt (S.scale (C.subsequence k))) ^ 3 *
        calibratedMetricVolume (C.limit.flow.metric 0)
          ((C.limit.flow.metric 0).ball C.limit.base (2 * a)) := by
  let : ConnectedSpace C.limit.carrier.carrier := C.limit.connectedSpace
  let g := C.limit.flow.metric 0
  let : PseudoEMetricSpace C.limit.carrier.carrier := g.comparisonPseudoEMetric
  let K := closure (g.ball C.limit.base (3 * a + 1))
  let V := g.ball C.limit.base (3 * a)
  have hK : IsCompact K := Proofs.M09.isCompact_closure_metric_ball g
    (C.limit.complete 0 C.limit.zero_mem) C.limit.base (3 * a + 1)
  have hV : IsOpen V := isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hVK : V ⊆ K := by
    intro x hx
    apply subset_closure
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hAV : g.ball C.limit.base (2 * a) ⊆ V := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  filter_upwards [C.eventually_pullback_inner_comparison_zero hK,
    C.eventually_source_ball_localization_zero a ha] with k hk hlocal
  apply (C.embedding k).source_ball_volume_le_of_localization
    (C.exhaustion.space_open k) (h0 k) (S.base_scalar_pos (C.subsequence k))
    g C.limit.base (C.base_preserving k (h0 k)) hV (hVK.trans hk.1) hAV
  · intro x hx
    obtain ⟨y, hy, hy0, he⟩ := hlocal x hx
    exact ⟨y, hy, he⟩
  · intro x hx v
    exact (hk.2 x (hVK hx) v).2

end PoincareConjecture.GeneralizedBlowupConvergence
