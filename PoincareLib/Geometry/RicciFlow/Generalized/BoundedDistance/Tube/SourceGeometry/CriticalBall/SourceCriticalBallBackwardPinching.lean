import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallBackwardRestriction
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Curvature.StrongNeckPinching
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Geometry.SourceFamilyScales

/-!
# Vanishing pinching error on the actual backward source family

The original base scalar diverges through the retained strict indices.
Original logarithmic pinching therefore makes the normalized negative
part tend to zero at every selected source point in the common backward
window. Morgan--Tian Claim 10.11, p. 255; M28 derivation 78.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {T : ∀ k, SourceTubeData (H.segment k)}
  {A1 : ℝ} {hA1 : 0 < A1} {phi : ℕ → ℕ}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))}
  {q : G.limitCarrier.carrier} {a : ℝ}
  (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a)

/-- The original base scalar used by the actual source normalization.
The family shift occurs exactly once (Claim 10.11; derivation 78). -/
def sourceBaseScalar (k : ℕ) : ℝ :=
  (E (D.sourceIndex k + H.shift)).flow.scalar
    ⟨(E (D.sourceIndex k + H.shift)).time, (E (D.sourceIndex k + H.shift)).basepoint⟩

/-- Every retained source has a positive normalization factor. -/
theorem sourceBaseScalar_pos (k : ℕ) : 0 < D.sourceBaseScalar k :=
  H.base_scalar_pos (D.sourceIndex k)

/-- Strict source selection, spatial extraction and finite-prefix removal
preserve divergence of the original base scalar (derivation 78). -/
theorem sourceBaseScalar_tendsto_atTop (hphi : StrictMono phi) :
    Tendsto D.sourceBaseScalar atTop atTop := by
  have hi : StrictMono D.sourceIndex :=
    hphi.comp (G.subsequence_strictMono.comp (fun _ _ h => Nat.add_lt_add_right h D.offset))
  exact H.base_scalar_tendsto_atTop.comp hi.tendsto_atTop

/-- The original physical point for a source flow at an included backward
time. Its dependent slice is retained literally (derivation 78). -/
def originalPoint (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-(a / 8)) 0)
    (x : strongNeckOpen (D.neck k)) : (E (D.sourceIndex k + H.shift)).flow.point :=
  GeneralizedStrongNeck.global_original_point (D.neck k) (D.sourceBaseScalar k)
    (D.sourceBaseScalar_pos k) (a / 8) (D.common_window k) t ht x

/-- The original negative part divided by the actual base scalar. -/
def pinchingError (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-(a / 8)) 0)
    (x : strongNeckOpen (D.neck k)) : ℝ :=
  LeviCivitaData.negativeCurvaturePart
    ((E (D.sourceIndex k + H.shift)).flow.connection (D.originalPoint k t ht x).1)
    (D.originalPoint k t ht x).2 / D.sourceBaseScalar k

set_option maxHeartbeats 1200000 in
-- The original point and connection retain the dependent selected slice.
/-- A uniform actual source curvature bound makes the original pinching
error vanish along arbitrary selected neck points, with time included.
Only equation (10.1) is used, in the original clock (derivation 78). -/
theorem pinchingError_tendsto_zero (P : RicciFlowCurvatureTheory.{u})
    (hphi : StrictMono phi) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ k t, t ∈ Icc (-(a / 8)) 0 → ∀ x : strongNeckOpen (D.neck k),
      ((D.sourceFlow k).connection t).curvatureTensorNorm x ≤ K)
    (t : ℝ) (ht : t ∈ Icc (-(a / 8)) 0)
    (x : ∀ k, strongNeckOpen (D.neck k)) :
    Tendsto (fun k => D.pinchingError k t ht (x k)) atTop (𝓝 0) := by
  apply Real.tendsto_zero_of_log_pinching (B := 9 * K) (by positivity)
    (D.sourceBaseScalar_tendsto_atTop hphi)
  · exact Eventually.of_forall fun _ => le_max_right _ _
  · apply Eventually.of_forall
    intro k
    exact GeneralizedStrongNeck.global_original_scalar_le_of_curvature_bound
      (D.neck k) (D.raw k) (D.sourceBaseScalar k) (D.sourceBaseScalar_pos k) P
      (a / 8) (by linarith [D.scale_pos]) (D.common_window k) t ht (x k) (hcurv k t ht (x k))
  · apply Eventually.of_forall
    intro k
    have htime := GeneralizedStrongNeck.global_original_point_time_mem
      (D.neck k) (D.sourceBaseScalar k) (D.sourceBaseScalar_pos k)
      (a / 8) (D.common_window k) t ht (x k)
    exact ((E (D.sourceIndex k + H.shift)).pinched _ htime
      (D.originalPoint k t ht (x k)).2).2

/-- The exact error controls source plane tensors with their actual metric
Gram determinant, including dependent vectors (Claim 10.11; derivation 78). -/
theorem sourceFlow_plane_lower (P : RicciFlowCurvatureTheory.{u})
    (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-(a / 8)) 0)
    (x : strongNeckOpen (D.neck k)) (v w : TangentSpace (𝓡 3) x) :
    -D.pinchingError k t ht x * M04.metricGram ((D.sourceFlow k).metric t) x v w ≤
      ((D.sourceFlow k).connection t).curvatureTensor x v w v w :=
  GeneralizedStrongNeck.global_flow_plane_lower (D.neck k) (D.raw k)
    (D.sourceBaseScalar k) (D.sourceBaseScalar_pos k) P (a / 8)
    (by linarith [D.scale_pos]) (D.common_window k) t ht x v w

end PoincareMT.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
