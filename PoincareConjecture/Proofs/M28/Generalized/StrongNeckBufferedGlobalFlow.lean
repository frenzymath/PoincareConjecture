import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckGlobalFlow










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

private def strongNeckBufferedInterval : SpacetimeInterval where
  domain := Icc (-(3 / 4 : ℝ)) 0
  ordConnected := ordConnected_Icc
  nontrivial := ⟨-(3 / 4 : ℝ), by norm_num, 0, by norm_num, by norm_num⟩

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
  (Q : ℝ) (hQ : 0 < Q)

include hQ



def GeneralizedStrongNeck.buffered_global_rescaling :
    OrdinaryParabolicRescaling (I := strongNeckBufferedInterval)
      (GeneralizedStrongNeck.rescaled_buffered_flow S H) (Q * S.scale ^ 2)
      (GeneralizedStrongNeck.global_scale_pos S Q hQ) 0 :=
  Classical.choice (M13.ordinaryParabolicRescaling strongNeckBufferedInterval
    (GeneralizedStrongNeck.rescaled_buffered_flow S H) (Q * S.scale ^ 2)
    (GeneralizedStrongNeck.global_scale_pos S Q hQ) 0)



theorem GeneralizedStrongNeck.buffered_global_time_mem {tau s : ℝ}
    (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8) (hs : s ∈ Icc (-tau) 0) :
    s / (Q * S.scale ^ 2) ∈ Icc (-(5 / 8 : ℝ)) 0 := by
  have ha := GeneralizedStrongNeck.global_scale_pos S Q hQ
  constructor
  · apply (le_div_iff₀ ha).2
    linarith only [hwindow, hs.1]
  · exact div_nonpos_of_nonpos_of_nonneg hs.2 ha.le



def GeneralizedStrongNeck.buffered_global_flow (tau : ℝ) (htau : 0 < tau)
    (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8) :
    RicciFlow 3 (strongNeckOpen S) (Icc (-tau) 0) := by
  let R := GeneralizedStrongNeck.buffered_global_rescaling S H Q hQ
  have hsub : Icc (-tau) 0 ⊆
      (parabolicInterval (Q * S.scale ^ 2)
        (GeneralizedStrongNeck.global_scale_pos S Q hQ) 0
        strongNeckBufferedInterval).domain := by
    intro s hs
    apply (mem_parabolicInterval_iff _ _ _ _ _).2
    have hcore := GeneralizedStrongNeck.buffered_global_time_mem S Q hQ hwindow hs
    change (0 + s / (Q * S.scale ^ 2)) ∈ Icc (-(3 / 4 : ℝ)) 0
    exact ⟨by linarith only [hcore.1], by simpa using hcore.2⟩
  exact Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow
    hsub ordConnected_Icc
    ⟨-tau, ⟨le_rfl, neg_nonpos.mpr htau.le⟩,
      0, ⟨neg_nonpos.mpr htau.le, le_rfl⟩, ne_of_lt (neg_lt_zero.mpr htau)⟩



theorem GeneralizedStrongNeck.buffered_global_flow_metric
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8)
    (s : ℝ) (x : strongNeckOpen S) (v w : TangentSpace (𝓡 3) x) :
    ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric s).inner
        x v w =
      (Q * S.scale ^ 2) *
        ((GeneralizedStrongNeck.rescaled_buffered_flow S H).metric
          (s / (Q * S.scale ^ 2))).inner x v w := by
  change ((GeneralizedStrongNeck.buffered_global_rescaling S H Q hQ).flow.metric s).inner
    x v w = _
  simpa only [parabolicTimeInv, zero_add] using
    (GeneralizedStrongNeck.buffered_global_rescaling S H Q hQ).metric_eq s x v w



@[simp] theorem GeneralizedStrongNeck.buffered_global_flow_connection
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8) (s : ℝ) :
    (GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).connection s =
      (GeneralizedStrongNeck.buffered_global_rescaling S H Q hQ).flow.connection s := rfl



theorem GeneralizedStrongNeck.buffered_global_flow_metric_at_zero
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8)
    (x : strongNeckOpen S) (v w : TangentSpace (𝓡 3) x) :
    ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric 0).inner
        x v w =
      Q * (F.metric t).inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x w) := by
  rw [GeneralizedStrongNeck.buffered_global_flow_metric, zero_div,
    GeneralizedStrongNeck.rescaled_buffered_flow_metric,
    GeneralizedStrongNeck.rescaled_metric_at_zero]
  field_simp [S.scale_pos.ne']



theorem GeneralizedStrongNeck.buffered_global_flow_metric_eq_restriction
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8) :
    (GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric 0 =
      intrinsicOpenMetric (M13.scaleSmoothMetric (F.metric t) Q hQ) (strongNeckOpen S) := by
  have hinner : ∀ (x : strongNeckOpen S) (v w : TangentSpace (𝓡 3) x),
      ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric 0).inner
          x v w =
        (intrinsicOpenMetric (M13.scaleSmoothMetric (F.metric t) Q hQ)
          (strongNeckOpen S)).inner x v w := by
    intro x v w
    rw [intrinsicOpenMetric_inner, M13.scaleSmoothMetric_inner]
    exact GeneralizedStrongNeck.buffered_global_flow_metric_at_zero
      S H Q hQ tau htau hwindow x v w
  cases h₁ : (GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).metric 0
  cases h₂ : intrinsicOpenMetric (M13.scaleSmoothMetric (F.metric t) Q hQ) (strongNeckOpen S)
  rw [h₁, h₂] at hinner
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  exact ContinuousLinearMap.ext (fun v => ContinuousLinearMap.ext (hinner x v))



theorem GeneralizedStrongNeck.buffered_global_physical_time_mem {tau s : ℝ}
    (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8) (hs : s ∈ Icc (-tau) 0) :
    t + s / Q ∈ F.interval := by
  have hcore := GeneralizedStrongNeck.buffered_global_time_mem S Q hQ hwindow hs
  have hsource : s / (Q * S.scale ^ 2) ∈ Ioc (-1 : ℝ) 0 :=
    ⟨by linarith only [hcore.1], hcore.2⟩
  rw [← GeneralizedStrongNeck.global_physical_time S Q hQ s]
  exact S.backward_time_mem hsource

end PoincareConjecture.M28
