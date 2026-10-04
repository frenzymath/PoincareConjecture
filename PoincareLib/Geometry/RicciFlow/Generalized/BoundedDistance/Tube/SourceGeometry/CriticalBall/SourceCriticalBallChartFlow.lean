import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Coordinates.StrongNeckChartFlow
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeCriticalRegion
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.ChartMaps

/-!
# Backward chart flows with the retained critical metric at time zero

The two open restrictions defining the actual critical metric commute
with the chart pullback. Consequently the original strong-neck flow,
globally rescaled and pulled back on a captured chart, has exactly that
critical metric at its terminal time. Morgan--Tian Proposition 5.14 and
Claims 10.10-10.11, pp. 90-91 and 254-255; M28 derivation 74.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
  (A1 : ℝ) (k : ℕ) (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
  [Nonempty U] (e : U → H.tubeCriticalRegion T A1 k)
  (he : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e)

include he in
/-- Composing the retained critical-region chart with both original open
inclusions is a local diffeomorphism into the tested slice (derivation 74). -/
theorem tubeCritical_chart_original_localDiffeomorph :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => (e x).val.val) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro x
  exact ((he x).comp (𝓡 3) (T k).carrierOpen
    (openSubtype_isLocalDiffeomorph (H.tubeCriticalRegion T A1 k) (e x))).comp
      (𝓡 3) ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier
      (openSubtype_isLocalDiffeomorph (T k).carrierOpen (e x).val)

variable (S : GeneralizedStrongNeck (E (k + H.shift)).flow
    (E (k + H.shift)).time epsilon)
  (R : RescaledRawCylinderData (C := (E (k + H.shift)).flow.slice
      (E (k + H.shift)).time)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
  (hcapture : ∀ x : U, (e x).val.val ∈ S.carrier)
  (tau : ℝ) (htau : 0 < tau)
  (hwindow : tau ≤ (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ * S.scale ^ 2 / 4)

/-- The actual captured-chart flow constructed with the original base
normalization, on its common closed interval (derivation 74). -/
def tubeCritical_chart_flow :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    RicciFlow 3 U (Icc (-tau) 0) :=
  GeneralizedStrongNeck.global_chart_flow S R
    ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩)
    (H.base_scalar_pos k) tau htau hwindow U hU (fun x : U => (e x).val.val)
    (H.tubeCritical_chart_original_localDiffeomorph T A1 k U hU e he) hcapture

/-- The terminal chart metric is exactly the actual critical metric
pulled back by the original retained chart, with both subtype inclusions
and the global base normalization accounted for (derivation 74). -/
theorem tubeCritical_chart_flow_metric_at_zero :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      ((H.tubeCritical_chart_flow T A1 k U hU e he S R hcapture
        tau htau hwindow).metric 0).inner x v w =
        (H.tubeCriticalMetric T A1 k).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro x v w
  let i₁ : H.tubeCriticalRegion T A1 k → (T k).carrierOpen := Subtype.val
  let i₂ : (T k).carrierOpen →
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier := Subtype.val
  have h₁ := openSubtype_isLocalDiffeomorph (H.tubeCriticalRegion T A1 k)
  have h₂ := openSubtype_isLocalDiffeomorph (T k).carrierOpen
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (fun y : U => (e y).val.val) x z =
        mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (e x))
          (mfderiv (𝓡 3) (𝓡 3) i₁ (e x) (mfderiv (𝓡 3) (𝓡 3) e x z)) := by
    have hfirst := mfderiv_comp_apply x ((h₁ (e x)).mdifferentiableAt (by simp))
      ((he x).mdifferentiableAt (by simp)) z
    have hsecond := mfderiv_comp_apply x ((h₂ (i₁ (e x))).mdifferentiableAt (by simp))
      (((he x).comp (𝓡 3) (T k).carrierOpen (h₁ (e x))).mdifferentiableAt (by simp)) z
    exact hsecond.trans (congrArg (mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (e x))) hfirst)
  change ((GeneralizedStrongNeck.global_chart_flow S R _ _ tau htau hwindow
    U hU _ _ hcapture).metric 0).inner x v w = _
  rw [GeneralizedStrongNeck.global_chart_flow_metric_at_zero, hderiv, hderiv]
  rfl

end PoincareMT.M28.CounterexampleNeckFamily
