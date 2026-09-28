import PoincareConjecture.Proofs.M28.Generalized.StrongNeckGlobalFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCurvatureCharts

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

include hQ

theorem GeneralizedStrongNeck.global_time_mem_backward {tau s : ℝ}
    (hwindow : tau ≤ Q * S.scale ^ 2 / 4) (hs : s ∈ Icc (-tau) 0) :
    s / (Q * S.scale ^ 2) ∈ Ioc (-1 : ℝ) 0 := by
  have h := GeneralizedStrongNeck.global_time_mem_quarter S Q hQ hwindow hs
  exact ⟨by linarith [h.1], h.2⟩

def GeneralizedStrongNeck.global_original_map (tau : ℝ)
    (hwindow : tau ≤ Q * S.scale ^ 2 / 4) (s : ℝ) (hs : s ∈ Icc (-tau) 0) :
    strongNeckOpen S →
      (F.slice (t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2))).carrier :=
  fun x => S.time_cylinder.forward (s / (Q * S.scale ^ 2))
    (GeneralizedStrongNeck.global_time_mem_backward S Q hQ hwindow hs) x.val

theorem GeneralizedStrongNeck.global_original_map_smooth (tau : ℝ)
    (hwindow : tau ≤ Q * S.scale ^ 2 / 4) (s : ℝ) (hs : s ∈ Icc (-tau) 0) :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs) :=
  (S.time_cylinder.forward_smooth _ _).comp_contMDiff contMDiff_subtype_val
    (fun x => x.property)

theorem GeneralizedStrongNeck.global_flow_metric_original
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S)
    (v w : TangentSpace (𝓡 3) x) :
    let f := GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs
    ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s).inner
      x v w =
      Q * (F.metric (t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2))).inner
        (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  let f := GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs
  let sigma := s / (Q * S.scale ^ 2)
  have hsig := GeneralizedStrongNeck.global_time_mem_backward S Q hQ hwindow hs
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) f x z =
        mfderiv (𝓡 3) (𝓡 3) (S.time_cylinder.forward sigma hsig) x.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x z) := by
    exact mfderiv_comp_apply x
      ((S.time_cylinder.forward_smooth sigma hsig).contMDiffAt
        (S.carrier_open.mem_nhds x.property) |>.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞) x).mdifferentiableAt (by simp)) z
  change _ = Q * (F.metric _).inner (f x)
    (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
  rw [GeneralizedStrongNeck.global_flow_metric,
    GeneralizedStrongNeck.rescaled_half_flow_metric,
    GeneralizedStrongNeck.rescaled_metric_at_time S H _ hsig, hderiv, hderiv]
  unfold GeneralizedFlowCylinder.pullbackInner
  dsimp only [f, GeneralizedStrongNeck.global_original_map, sigma]
  field_simp [S.scale_pos.ne']

theorem GeneralizedStrongNeck.global_flow_scalar_original
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S) :
    let f := GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs
    ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s).scalarCurvature
      x = (F.connection (t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2))).scalarCurvature
        (f x) / Q := by
  let f := GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs
  let time := t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2)
  let D := (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s
  let DQ := M13.scaleLeviCivitaData (F.connection time) Q hQ
  have hmetric : ∀ y ∈ (univ : Set (strongNeckOpen S)),
      ∀ a b : TangentSpace (𝓡 3) y,
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s).inner
          y a b = (M13.scaleSmoothMetric (F.metric time) Q hQ).inner
            (f y) (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b) := by
    intro y _ a b
    exact GeneralizedStrongNeck.global_flow_metric_original S H Q hQ tau htau hwindow
      s hs y a b
  have hi := D.scalarCurvature_eq_of_local_isometry DQ isOpen_univ
    (GeneralizedStrongNeck.global_original_map_smooth S Q hQ tau hwindow s hs).contMDiffOn
    hmetric (mem_univ x)
  have hh := M13.homothety_scalarCurvature_eq
    (F.metric time) (M13.scaleSmoothMetric (F.metric time) Q hQ)
    (Diffeomorph.refl (𝓡 3) (F.slice time).carrier ∞) Q hQ
    (M13.identity_metricHomothety (F.metric time) Q hQ) (F.connection time) DQ (f x)
  exact hi.trans hh

theorem GeneralizedStrongNeck.global_flow_curvatureTensor_original
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : strongNeckOpen S)
    (v w y z : TangentSpace (𝓡 3) x) :
    let f := GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs
    ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s).curvatureTensor
      x v w y z =
      Q * (F.connection (t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2))).curvatureTensor (f x)
          (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
          (mfderiv (𝓡 3) (𝓡 3) f x y) (mfderiv (𝓡 3) (𝓡 3) f x z) := by
  let f := GeneralizedStrongNeck.global_original_map S Q hQ tau hwindow s hs
  let time := t + (s / (Q * S.scale ^ 2)) / (S.scale⁻¹ ^ 2)
  let D := (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s
  let DQ := M13.scaleLeviCivitaData (F.connection time) Q hQ
  have hmetric : ∀ a ∈ (univ : Set (strongNeckOpen S)),
      ∀ b c : TangentSpace (𝓡 3) a,
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s).inner
          a b c = (M13.scaleSmoothMetric (F.metric time) Q hQ).inner
            (f a) (mfderiv (𝓡 3) (𝓡 3) f a b) (mfderiv (𝓡 3) (𝓡 3) f a c) := by
    intro a _ b c
    exact GeneralizedStrongNeck.global_flow_metric_original S H Q hQ tau htau hwindow
      s hs a b c
  have hi := D.curvatureTensor_eq_of_local_isometry DQ isOpen_univ
    (GeneralizedStrongNeck.global_original_map_smooth S Q hQ tau hwindow s hs).contMDiffOn
    hmetric (mem_univ x) v w y z
  have hh := M13.homothety_curvatureTensor_eq
    (F.metric time) (M13.scaleSmoothMetric (F.metric time) Q hQ)
    (Diffeomorph.refl (𝓡 3) (F.slice time).carrier ∞) Q
    (M13.identity_metricHomothety (F.metric time) Q hQ) (F.connection time) DQ (f x)
    (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
    (mfderiv (𝓡 3) (𝓡 3) f x y) (mfderiv (𝓡 3) (𝓡 3) f x z)
  change DQ.curvatureTensor (f x)
    (mfderiv (𝓡 3) (𝓡 3) id (f x) (mfderiv (𝓡 3) (𝓡 3) f x v))
    (mfderiv (𝓡 3) (𝓡 3) id (f x) (mfderiv (𝓡 3) (𝓡 3) f x w))
    (mfderiv (𝓡 3) (𝓡 3) id (f x) (mfderiv (𝓡 3) (𝓡 3) f x y))
    (mfderiv (𝓡 3) (𝓡 3) id (f x) (mfderiv (𝓡 3) (𝓡 3) f x z)) = _ at hh
  simp only [mfderiv_id] at hh
  exact hi.trans hh

end PoincareConjecture.M28
