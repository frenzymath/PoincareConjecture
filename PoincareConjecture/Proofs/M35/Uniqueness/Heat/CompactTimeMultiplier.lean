import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousTimeMultiplier
import Mathlib.Topology.ContinuousMap.Compact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped BoundedContinuousFunction

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def timeIntervalExtension {T : ℝ} (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, E) →L[ℝ] (ℝ →ᵇ E) := by
  let B := ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) T) E ℝ
  exact (BoundedContinuousFunction.compContinuousCLM E ℝ
    ⟨projIcc 0 T hT, continuous_projIcc⟩).comp B.toContinuousLinearEquiv.toContinuousLinearMap

theorem timeIntervalExtension_apply {T : ℝ} (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, E)) (t : ℝ) :
    timeIntervalExtension hT A t = A (projIcc 0 T hT t) := rfl

theorem timeIntervalExtension_apply_mem {T : ℝ} (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, E)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeIntervalExtension hT A t = A ⟨t, ht⟩ := by
  rw [timeIntervalExtension_apply, projIcc_of_mem hT ht]

def compactTimeLp {T : ℝ} (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, E →L[ℝ] F) →L[ℝ]
      (Lp E 2 (SpectralHeatNative.timeMeasure T) →L[ℝ]
        Lp F 2 (SpectralHeatNative.timeMeasure T)) :=
  (continuousTimeLp (SpectralHeatNative.timeMeasure T)).comp (timeIntervalExtension hT)

theorem compactTimeLp_coe {T : ℝ} (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : Lp E 2 (SpectralHeatNative.timeMeasure T)) :
    ∀ᵐ t ∂SpectralHeatNative.timeMeasure T, ∀ ht : t ∈ Icc 0 T,
      compactTimeLp hT A u t = A ⟨t, ht⟩ (u t) := by
  filter_upwards [continuousTimeLp_coe (SpectralHeatNative.timeMeasure T)
    (timeIntervalExtension hT A) u] with t ht htime
  rw [show compactTimeLp hT A u t =
    continuousTimeLp (SpectralHeatNative.timeMeasure T) (timeIntervalExtension hT A) u t from rfl,
    ht, timeIntervalExtension_apply_mem hT A htime]

end PoincareConjecture.M35.Uniqueness.Heat
