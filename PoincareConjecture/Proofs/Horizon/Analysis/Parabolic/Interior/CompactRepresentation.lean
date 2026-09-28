import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactSlices
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.DuhamelRepresentation








noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open MeasureTheory Set
open scoped ContDiff Topology

namespace Poincare.Parabolic.Interior

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in

def heatResidual (f : V × ℝ → F) (p : V × ℝ) : F :=
  timeDerivative f p - Kernel.lapEval (spatialDerivative (spatialDerivative f) p)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
theorem contDiff_heatResidual {f : V × ℝ → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (heatResidual f) :=
  (contDiff_timeDerivative hf).sub ((Kernel.lapEval (V := V) (F := F)).contDiff.comp
    (contDiff_spatialDerivative (contDiff_spatialDerivative hf)))

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
theorem hasCompactSupport_heatResidual {f : V × ℝ → F} (hf : HasCompactSupport f) :
    HasCompactSupport (heatResidual f) :=
  (hasCompactSupport_timeDerivative hf).sub
    ((hasCompactSupport_spatialDerivative (hasCompactSupport_spatialDerivative hf)).comp_left
      (g := Kernel.lapEval) (map_zero _))



theorem heatDuh_compactSlice_residual {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hzero : ∀ x, f (x, 0) = 0) {t : ℝ} (ht : 0 < t) (x : V) :
    Kernel.heatDuh t
      (compactSlice (heatResidual f) (contDiff_heatResidual hf).continuous
        (hasCompactSupport_heatResidual hc)) x = f (x, t) := by
  let u := compactSlice f hf.continuous hc
  let dt := compactSlice (timeDerivative f) (contDiff_timeDerivative hf).continuous
    (hasCompactSupport_timeDerivative hc)
  let dx := compactSlice (spatialDerivative f) (contDiff_spatialDerivative hf).continuous
    (hasCompactSupport_spatialDerivative hc)
  let dxx := compactSlice (spatialDerivative (spatialDerivative f))
    (contDiff_spatialDerivative (contDiff_spatialDerivative hf)).continuous
    (hasCompactSupport_spatialDerivative (hasCompactSupport_spatialDerivative hc))
  let source := compactSlice (heatResidual f) (contDiff_heatResidual hf).continuous
    (hasCompactSupport_heatResidual hc)
  have hsource : (fun s => dt s - Kernel.coreLap (dxx s)) = source := by
    funext s
    ext y
    rfl
  have hsourceCont : Continuous source :=
    continuous_compactSlice (contDiff_heatResidual hf) (hasCompactSupport_heatResidual hc)
  have hint : IntervalIntegrable (fun s => Kernel.heatScaled (t - s) (source s) x)
      volume 0 t := by
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.mpr
    intro s
    exact Kernel.tendsto_heatScaled_of_tendsto
      (continuous_const.sub continuous_id).continuousAt hsourceCont.continuousAt x
  have h := Kernel.heatDuh_eq_of_zero_initial ht u dt dx dxx
    (fun s _ => hasDerivAt_compactSlice hf hc s)
    (fun s _ y => hasFDerivAt_spatialSlice (hf.differentiable (by simp)) y s)
    (fun s _ y => hasFDerivAt_spatialSlice
      ((contDiff_spatialDerivative hf).differentiable (by simp)) y s)
    (continuous_compactSlice hf hc) (by ext y; exact hzero y) x
    (by simpa only [congrFun hsource] using hint)
  simpa only [hsource, u, source, compactSlice_apply] using h

end Poincare.Parabolic.Interior
