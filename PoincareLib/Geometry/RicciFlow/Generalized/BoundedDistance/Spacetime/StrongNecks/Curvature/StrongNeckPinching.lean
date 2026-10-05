import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckPhysicalReadout
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Pinching.Geometry.GramLowerBound
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Pinching.Basic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.TensorEvaluationBound

/-!
# Original pinching on the actual globally normalized neck

The actual cylinder point retains its original clock. The four-tensor
readout gives a Gram-weighted lower bound with error nu/Q, and the scalar
readout permits the original logarithmic pinching estimate. Morgan--Tian
Claim 10.11, p. 255, and M28 derivation 78.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
  (Q : ℝ) (hQ : 0 < Q)

/-- The actual original spacetime point corresponding to an included
globally normalized source point (Claim 10.11; derivation 78). -/
def GeneralizedStrongNeck.global_original_point (tau : ℝ)
    (hwindow : tau ≤ Q * S.scale ^ 2 / 4) (s : ℝ) (hs : s ∈ Icc (-tau) 0)
    (x : strongNeckOpen S) : F.point :=
  ⟨t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2),
    GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs x⟩

/-- The original strong neck supplies interval membership for the literal
physical point, including both endpoints of the smaller window. -/
theorem GeneralizedStrongNeck.global_original_point_time_mem (tau : ℝ)
    (hwindow : tau ≤ Q * S.scale ^ 2 / 4) (s : ℝ) (hs : s ∈ Icc (-tau) 0)
    (x : strongNeckOpen S) :
    (GeneralizedStrongNeck.global_original_point S Q hQ tau hwindow s hs x).1 ∈
      F.interval :=
  S.backward_time_mem (GeneralizedStrongNeck.global_time_mem_backward S Q hQ hwindow hs)

/-- Pulling the original Gram bound through the same cylinder gives the
normalized error nu/Q on every pair of source vectors (derivation 78). -/
theorem GeneralizedStrongNeck.global_flow_plane_lower
    (P : RicciFlowCurvatureTheory.{u})
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S)
    (v w : TangentSpace (𝓡 3) x) :
    let p := GeneralizedStrongNeck.global_original_point S Q hQ tau hwindow s hs x;
    -((F.connection p.1).negativeCurvaturePart p.2 / Q) *
        M04.metricGram
          ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s) x v w ≤
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s).curvatureTensor
        x v w v w := by
  let p := GeneralizedStrongNeck.global_original_point S Q hQ tau hwindow s hs x
  let f := GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs
  let dv := mfderiv (𝓡 3) (𝓡 3) f x v
  let dw := mfderiv (𝓡 3) (𝓡 3) f x w
  let g := (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s
  have hgram : M04.metricGram g x v w = Q ^ 2 * M04.metricGram (F.metric p.1) p.2 dv dw := by
    unfold M04.metricGram
    dsimp only [g]
    rw [GeneralizedStrongNeck.global_flow_metric_original S H Q hQ tau htau hwindow s hs,
      GeneralizedStrongNeck.global_flow_metric_original S H Q hQ tau htau hwindow s hs,
      GeneralizedStrongNeck.global_flow_metric_original S H Q hQ tau htau hwindow s hs]
    dsimp only [p, GeneralizedStrongNeck.global_original_point, dv, dw, f]
    ring
  have hbase := (F.connection p.1).curvatureTensor_plane_ge_negativePart_mul_gram
    (P.tensor_calculus 3 (F.slice p.1).carrier (F.metric p.1) (F.connection p.1)) p.2 dv dw
  calc
    -((F.connection p.1).negativeCurvaturePart p.2 / Q) * M04.metricGram g x v w =
        Q * (-(F.connection p.1).negativeCurvaturePart p.2 *
          M04.metricGram (F.metric p.1) p.2 dv dw) := by
      rw [hgram]
      field_simp [hQ.ne']
    _ ≤ Q * (F.connection p.1).curvatureTensor p.2 dv dw dv dw :=
      mul_le_mul_of_nonneg_left hbase hQ.le
    _ = _ := (GeneralizedStrongNeck.global_flow_curvatureTensor_original S H Q hQ
      tau htau hwindow s hs x v w v w).symm

/-- A curvature bound on the actual normalized source yields the original
scalar bound needed for logarithmic pinching (Claim 10.11; derivation 78). -/
theorem GeneralizedStrongNeck.global_original_scalar_le_of_curvature_bound
    (P : RicciFlowCurvatureTheory.{u})
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S) {K : ℝ}
    (hcurv : LeviCivitaData.curvatureTensorNorm
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s) x ≤ K) :
    F.scalar (GeneralizedStrongNeck.global_original_point S Q hQ tau hwindow s hs x) ≤
      (9 * K) * Q := by
  let p := GeneralizedStrongNeck.global_original_point S Q hQ tau hwindow s hs x
  let g := (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s
  let D := (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s
  have hscalar : D.scalarCurvature x ≤ 9 * K := by
    calc
      D.scalarCurvature x ≤ |D.scalarCurvature x| := le_abs_self _
      _ ≤ (3 : ℝ) ^ 2 * D.curvatureTensorNorm x :=
        Proofs.M09.scalar_abs_le_curvatureTensorNorm P g D x
      _ ≤ (3 : ℝ) ^ 2 * K := mul_le_mul_of_nonneg_left hcurv (sq_nonneg _)
      _ = 9 * K := by norm_num
  have hread := GeneralizedStrongNeck.global_flow_scalar_original S H Q hQ
    tau htau hwindow s hs x
  change D.scalarCurvature x = F.scalar p / Q at hread
  exact (div_le_iff₀ hQ).mp (hread ▸ hscalar)

/-- Original pinching bounds the original negative part uniformly once Q
exceeds a threshold determined by the normalized curvature bound. No
pinching assertion is made at a negative absolute time (derivation 78). -/
theorem GeneralizedStrongNeck.global_original_negativePart_lt
    (P : RicciFlowCurvatureTheory.{u}) (hpinch : generalizedHamiltonIveyPinched F)
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S)
    {K eta : ℝ} (hK : 0 ≤ K) (heta : 0 < eta)
    (hlarge : Real.exp (3 + (9 * K + 1) / (2 * eta)) / eta ≤ Q)
    (hcurv : LeviCivitaData.curvatureTensorNorm
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s) x ≤ K) :
    let p := GeneralizedStrongNeck.global_original_point S Q hQ tau hwindow s hs x
    (F.connection p.1).negativeCurvaturePart p.2 < eta * Q := by
  let p := GeneralizedStrongNeck.global_original_point S Q hQ tau hwindow s hs x
  exact hpinch.weak.negative_part_lt heta (by positivity) hlarge
    (GeneralizedStrongNeck.global_original_point_time_mem S Q hQ tau hwindow s hs x) p.2
    (GeneralizedStrongNeck.global_original_scalar_le_of_curvature_bound S H Q hQ P
      tau htau hwindow s hs x hcurv)

end PoincareMT.M28
