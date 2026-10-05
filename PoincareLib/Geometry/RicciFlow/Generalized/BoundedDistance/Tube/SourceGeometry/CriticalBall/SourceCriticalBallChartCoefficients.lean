import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallChartFlow
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients

/-!
# Terminal coefficients of the original backward source flows

Canonical parametrizations of the captured neck map and retained critical
map have exactly the same terminal coefficients. The equality holds on
the open chart, so it can be differentiated on a smaller compact set.
Morgan--Tian Claims 10.10-10.11, pp. 254-255; M28 derivation 76.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareMT.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 1600000 in
-- The two dependent pullback metrics retain the same original raw witness.
/-- The actual global source flow and the critical metric have identical
terminal coefficients under their corresponding canonical parametrizations.
Both maps use the same retained chart (derivation 76). -/
theorem tubeCritical_global_flow_terminal_coefficients
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    (A1 : ℝ) (k : ℕ) (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    [Nonempty U] (e : U → H.tubeCriticalRegion T A1 k)
    (he : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e)
    (S : GeneralizedStrongNeck (E (k + H.shift)).flow
      (E (k + H.shift)).time epsilon)
    (R : RescaledRawCylinderData (C := (E (k + H.shift)).flow.slice
        (E (k + H.shift)).time)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
    (hcapture : ∀ x : U, (e x).val.val ∈ S.carrier)
    (tau : ℝ) (htau : 0 < tau)
    (hwindow : tau ≤ (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ * S.scale ^ 2 / 4) :
    EqOn (((GeneralizedStrongNeck.global_flow S R
      ((E (k + H.shift)).flow.scalar
        ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩)
      (H.base_scalar_pos k) tau htau hwindow).metric 0).pullbackCoefficients
        (chartParametrization (fun _ : Unit => U) (fun _ => hU)
          (i := ()) (GeneralizedStrongNeck.captured_chart_map S U
            (fun x : U => (e x).val.val) hcapture)))
      ((H.tubeCriticalMetric T A1 k).pullbackCoefficients
        (chartParametrization (fun _ : Unit => U) (fun _ => hU) (i := ()) e)) U := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let f := GeneralizedStrongNeck.captured_chart_map S U
    (fun x : U => (e x).val.val) hcapture
  have hf := GeneralizedStrongNeck.captured_chart_map_localDiffeomorph S U hU
    (fun x : U => (e x).val.val)
    (H.tubeCritical_chart_original_localDiffeomorph T A1 k U hU e he) hcapture
  intro z hz
  let x : U := ⟨z, hz⟩
  have hd₁ := mfderiv_chartParametrization (fun _ : Unit => U) (fun _ => hU)
    (i := ()) x (hf.contMDiff x)
  have hd₂ := mfderiv_chartParametrization (fun _ : Unit => U) (fun _ => hU)
    (i := ()) x (he.contMDiff x)
  ext v w
  change ((GeneralizedStrongNeck.global_flow S R _ _ tau htau hwindow).metric 0).inner
    (chartParametrization (fun _ : Unit => U) (fun _ => hU) (i := ()) f x)
    (mfderiv (𝓡 3) (𝓡 3)
      (chartParametrization (fun _ : Unit => U) (fun _ => hU) (i := ()) f) x v)
    (mfderiv (𝓡 3) (𝓡 3)
      (chartParametrization (fun _ : Unit => U) (fun _ => hU) (i := ()) f) x w) = _
  change _ = (H.tubeCriticalMetric T A1 k).inner
    (chartParametrization (fun _ : Unit => U) (fun _ => hU) (i := ()) e x)
    (mfderiv (𝓡 3) (𝓡 3)
      (chartParametrization (fun _ : Unit => U) (fun _ => hU) (i := ()) e) x v)
    (mfderiv (𝓡 3) (𝓡 3)
      (chartParametrization (fun _ : Unit => U) (fun _ => hU) (i := ()) e) x w)
  rw [chartParametrization_apply, chartParametrization_apply, hd₁, hd₂]
  exact H.tubeCritical_chart_flow_metric_at_zero T A1 k U hU e he S R
    hcapture tau htau hwindow x v w

end PoincareMT.M28.CounterexampleNeckFamily
