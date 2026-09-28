import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedPhysicalReadout
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching.GramLowerBound
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching
import PoincareConjecture.Proofs.M09.TensorEvaluationBound










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
  (Q : ℝ) (hQ : 0 < Q)



def GeneralizedStrongNeck.buffered_global_original_point (tau : ℝ)
    (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8) (s : ℝ) (hs : s ∈ Icc (-tau) 0)
    (x : strongNeckOpen S) : F.point :=
  ⟨t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2),
    GeneralizedStrongNeck.buffered_global_original_map S Q hQ tau hwindow s hs x⟩



theorem GeneralizedStrongNeck.buffered_global_original_point_time_mem (tau : ℝ)
    (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8) (s : ℝ) (hs : s ∈ Icc (-tau) 0)
    (x : strongNeckOpen S) :
    (GeneralizedStrongNeck.buffered_global_original_point S Q hQ tau hwindow s hs x).1 ∈
      F.interval :=
  S.backward_time_mem (GeneralizedStrongNeck.buffered_global_time_mem_backward S Q hQ hwindow hs)



theorem GeneralizedStrongNeck.buffered_global_flow_plane_lower
    (P : RicciFlowCurvatureTheory.{u})
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S)
    (v w : TangentSpace (𝓡 3) x) :
    let p := GeneralizedStrongNeck.buffered_global_original_point S Q hQ tau hwindow s hs x;
    -((F.connection p.1).negativeCurvaturePart p.2 / Q) *
        M04.metricGram
          ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric s) x v w ≤
      ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).connection
        s).curvatureTensor
        x v w v w := by
  let p := GeneralizedStrongNeck.buffered_global_original_point S Q hQ tau hwindow s hs x
  let f := GeneralizedStrongNeck.buffered_global_original_map S Q hQ tau hwindow s hs
  let dv := mfderiv (𝓡 3) (𝓡 3) f x v
  let dw := mfderiv (𝓡 3) (𝓡 3) f x w
  let g := (GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric s
  have hgram : M04.metricGram g x v w = Q ^ 2 * M04.metricGram (F.metric p.1) p.2 dv dw := by
    unfold M04.metricGram
    dsimp only [g]
    rw [GeneralizedStrongNeck.buffered_global_flow_metric_original S H Q hQ tau htau hwindow s hs,
      GeneralizedStrongNeck.buffered_global_flow_metric_original S H Q hQ tau htau hwindow s hs,
      GeneralizedStrongNeck.buffered_global_flow_metric_original S H Q hQ tau htau hwindow s hs]
    dsimp only [p, GeneralizedStrongNeck.buffered_global_original_point, dv, dw, f]
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
    _ = _ := (GeneralizedStrongNeck.buffered_global_flow_curvatureTensor_original S H Q hQ
      tau htau hwindow s hs x v w v w).symm



theorem GeneralizedStrongNeck.buffered_global_original_scalar_le_of_curvature_bound
    (P : RicciFlowCurvatureTheory.{u})
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S) {K : ℝ}
    (hcurv : LeviCivitaData.curvatureTensorNorm
      ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).connection s) x ≤ K) :
    F.scalar (GeneralizedStrongNeck.buffered_global_original_point S Q hQ tau hwindow s hs x) ≤
      (9 * K) * Q := by
  let p := GeneralizedStrongNeck.buffered_global_original_point S Q hQ tau hwindow s hs x
  let g := (GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric s
  let D := (GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).connection s
  have hscalar : D.scalarCurvature x ≤ 9 * K := by
    calc
      D.scalarCurvature x ≤ |D.scalarCurvature x| := le_abs_self _
      _ ≤ (3 : ℝ) ^ 2 * D.curvatureTensorNorm x :=
        Proofs.M09.scalar_abs_le_curvatureTensorNorm P g D x
      _ ≤ (3 : ℝ) ^ 2 * K := mul_le_mul_of_nonneg_left hcurv (sq_nonneg _)
      _ = 9 * K := by norm_num
  have hread := GeneralizedStrongNeck.buffered_global_flow_scalar_original S H Q hQ
    tau htau hwindow s hs x
  change D.scalarCurvature x = F.scalar p / Q at hread
  exact (div_le_iff₀ hQ).mp (hread ▸ hscalar)




theorem GeneralizedStrongNeck.buffered_global_original_negativePart_lt
    (P : RicciFlowCurvatureTheory.{u}) (hpinch : generalizedHamiltonIveyPinched F)
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S)
    {K eta : ℝ} (hK : 0 ≤ K) (heta : 0 < eta)
    (hlarge : Real.exp (3 + (9 * K + 1) / (2 * eta)) / eta ≤ Q)
    (hcurv : LeviCivitaData.curvatureTensorNorm
      ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).connection s) x ≤ K) :
    let p := GeneralizedStrongNeck.buffered_global_original_point S Q hQ tau hwindow s hs x
    (F.connection p.1).negativeCurvaturePart p.2 < eta * Q := by
  let p := GeneralizedStrongNeck.buffered_global_original_point S Q hQ tau hwindow s hs x
  exact hpinch.weak.negative_part_lt heta (by positivity) hlarge
    (GeneralizedStrongNeck.buffered_global_original_point_time_mem S Q hQ tau hwindow s hs x) p.2
    (GeneralizedStrongNeck.buffered_global_original_scalar_le_of_curvature_bound S H Q hQ P
      tau htau hwindow s hs x hcurv)

end PoincareConjecture.M28
