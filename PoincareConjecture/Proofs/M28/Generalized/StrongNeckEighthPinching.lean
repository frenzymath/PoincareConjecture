import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCenterLimits
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckPinching













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))


theorem GeneralizedStrongNeck.rescaled_secondary_scale_eq_one :
    S.scale⁻¹ ^ 2 * S.scale ^ 2 = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ S.scale_pos.ne', one_pow]


theorem GeneralizedStrongNeck.rescaled_eighth_global_window :
    (1 / 8 : ℝ) ≤ (S.scale⁻¹ ^ 2 * S.scale ^ 2) / 4 := by
  rw [GeneralizedStrongNeck.rescaled_secondary_scale_eq_one S]
  norm_num



theorem GeneralizedStrongNeck.global_flow_metric_eq_half_of_unit_scale
    (Q : ℝ) (hQ : 0 < Q) (hunit : Q * S.scale ^ 2 = 1)
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4) (s : ℝ) :
    (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s =
      (GeneralizedStrongNeck.rescaled_half_flow S H).metric s := by
  have hinner : ∀ (x : strongNeckOpen S) (v w : TangentSpace (𝓡 3) x),
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s).inner
        x v w = ((GeneralizedStrongNeck.rescaled_half_flow S H).metric s).inner x v w := by
    intro x v w
    simpa only [hunit, div_one, one_mul] using
      GeneralizedStrongNeck.global_flow_metric S H Q hQ tau htau hwindow s x v w
  cases h₁ : (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s
  cases h₂ : (GeneralizedStrongNeck.rescaled_half_flow S H).metric s
  rw [h₁, h₂] at hinner
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  exact ContinuousLinearMap.ext (fun v => ContinuousLinearMap.ext (hinner x v))



theorem GeneralizedStrongNeck.global_flow_curvature_eq_half_of_unit_scale
    (Q : ℝ) (hQ : 0 < Q) (hunit : Q * S.scale ^ 2 = 1)
    (tau : ℝ) (htau : 0 < tau) (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
    (s : ℝ) (x : strongNeckOpen S) :
    (∀ v w y z : TangentSpace (𝓡 3) x,
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s).curvatureTensor
        x v w y z =
      ((GeneralizedStrongNeck.rescaled_half_flow S H).connection s).curvatureTensor x v w y z) ∧
    ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s).curvatureTensorNorm
      x =
      ((GeneralizedStrongNeck.rescaled_half_flow S H).connection s).curvatureTensorNorm x := by
  have heq := GeneralizedStrongNeck.global_flow_metric_eq_half_of_unit_scale
    S H Q hQ hunit tau htau hwindow s
  have hmetric : ∀ y ∈ (univ : Set (strongNeckOpen S)),
      ∀ v w : TangentSpace (𝓡 3) y,
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric s).inner y v w =
        ((GeneralizedStrongNeck.rescaled_half_flow S H).metric s).inner (id y)
          (mfderiv (𝓡 3) (𝓡 3) id y v) (mfderiv (𝓡 3) (𝓡 3) id y w) := by
    intro y _ v w
    simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
      congrArg (fun g : RiemannianMetric 3 (strongNeckOpen S) => g.inner y v w) heq
  constructor
  · intro v w y z
    simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
      ((GeneralizedStrongNeck.global_flow
        S H Q hQ tau htau hwindow).connection s).curvatureTensor_eq_of_local_isometry
          ((GeneralizedStrongNeck.rescaled_half_flow S H).connection s)
          isOpen_univ contMDiff_id.contMDiffOn hmetric (mem_univ x) v w y z
  · exact ((GeneralizedStrongNeck.global_flow
      S H Q hQ tau htau hwindow).connection s).curvatureTensorNorm_eq_of_local_isometry
        ((GeneralizedStrongNeck.rescaled_half_flow S H).connection s)
        isOpen_univ contMDiff_id.contMDiffOn hmetric (mem_univ x)


@[simp] theorem GeneralizedStrongNeck.rescaled_eighth_flow_metric (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_eighth_flow S H).metric s =
      (GeneralizedStrongNeck.rescaled_half_flow S H).metric s := rfl


@[simp] theorem GeneralizedStrongNeck.rescaled_eighth_flow_connection (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_eighth_flow S H).connection s =
      (GeneralizedStrongNeck.rescaled_half_flow S H).connection s := rfl


def GeneralizedStrongNeck.rescaled_eighth_original_point
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) : F.point :=
  GeneralizedStrongNeck.global_original_point S (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos
    (1 / 8) (GeneralizedStrongNeck.rescaled_eighth_global_window S) s hs x


theorem GeneralizedStrongNeck.rescaled_eighth_original_point_eq_pointMap
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) :
    GeneralizedStrongNeck.rescaled_eighth_original_point S s hs x =
      S.time_cylinder.pointMap s (show s ∈ Ioc (-1 : ℝ) 0 from
        ⟨by linarith [hs.1], hs.2⟩) x.val := by
  have hscaled := GeneralizedStrongNeck.global_time_mem_backward S (S.scale⁻¹ ^ 2)
    S.time_cylinder.scale_pos (GeneralizedStrongNeck.rescaled_eighth_global_window S) hs
  have htime : s ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith [hs.1], hs.2⟩
  exact congrArg (fun u : Ioc (-1 : ℝ) 0 =>
    S.time_cylinder.pointMap u.val u.property x.val)
      (show (⟨s / (S.scale⁻¹ ^ 2 * S.scale ^ 2), hscaled⟩ : Ioc (-1 : ℝ) 0) =
          ⟨s, htime⟩ from Subtype.ext (by
            change s / (S.scale⁻¹ ^ 2 * S.scale ^ 2) = s
            rw [GeneralizedStrongNeck.rescaled_secondary_scale_eq_one S, div_one]))


theorem GeneralizedStrongNeck.rescaled_eighth_original_point_time
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) :
    (GeneralizedStrongNeck.rescaled_eighth_original_point S s hs x).1 = t + s * S.scale ^ 2 := by
  change t + (s / (S.scale⁻¹ ^ 2 * S.scale ^ 2)) / (S.scale⁻¹ ^ 2) = _
  rw [GeneralizedStrongNeck.rescaled_secondary_scale_eq_one S, div_one]
  field_simp [S.scale_pos.ne']


theorem GeneralizedStrongNeck.rescaled_eighth_original_point_time_mem
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) :
    (GeneralizedStrongNeck.rescaled_eighth_original_point S s hs x).1 ∈ F.interval :=
  GeneralizedStrongNeck.global_original_point_time_mem S (S.scale⁻¹ ^ 2)
    S.time_cylinder.scale_pos (1 / 8) (GeneralizedStrongNeck.rescaled_eighth_global_window S)
    s hs x


theorem GeneralizedStrongNeck.rescaled_eighth_physical_time_mem
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) :
    t + s * S.scale ^ 2 ∈ F.interval := by
  rw [← GeneralizedStrongNeck.rescaled_eighth_original_point_time S s hs x]
  exact GeneralizedStrongNeck.rescaled_eighth_original_point_time_mem S s hs x


def GeneralizedStrongNeck.rescaled_eighth_pinching_error
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) : ℝ :=
  let p := GeneralizedStrongNeck.rescaled_eighth_original_point S s hs x
  (F.connection p.1).negativeCurvaturePart p.2 / (S.scale⁻¹ ^ 2)


theorem GeneralizedStrongNeck.rescaled_eighth_pinching_error_nonneg
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) :
    0 ≤ GeneralizedStrongNeck.rescaled_eighth_pinching_error S s hs x :=
  div_nonneg (le_max_right _ _) S.time_cylinder.scale_pos.le


theorem GeneralizedStrongNeck.rescaled_half_plane_lower_eighth_window
    (P : RicciFlowCurvatureTheory.{u})
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S)
    (v w : TangentSpace (𝓡 3) x) :
    -GeneralizedStrongNeck.rescaled_eighth_pinching_error S s hs x *
        M04.metricGram ((GeneralizedStrongNeck.rescaled_half_flow S H).metric s) x v w ≤
      ((GeneralizedStrongNeck.rescaled_half_flow S H).connection s).curvatureTensor x v w v w := by
  have hmetric := GeneralizedStrongNeck.global_flow_metric_eq_half_of_unit_scale
    S H (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos
    (GeneralizedStrongNeck.rescaled_secondary_scale_eq_one S) (1 / 8) (by norm_num)
    (GeneralizedStrongNeck.rescaled_eighth_global_window S) s
  have hgram := congrArg
    (fun g : RiemannianMetric 3 (strongNeckOpen S) => M04.metricGram g x v w) hmetric
  have htensor := (GeneralizedStrongNeck.global_flow_curvature_eq_half_of_unit_scale
    S H (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos
    (GeneralizedStrongNeck.rescaled_secondary_scale_eq_one S) (1 / 8) (by norm_num)
    (GeneralizedStrongNeck.rescaled_eighth_global_window S) s x).1 v w v w
  have h := GeneralizedStrongNeck.global_flow_plane_lower
    S H (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos P (1 / 8) (by norm_num)
    (GeneralizedStrongNeck.rescaled_eighth_global_window S) s hs x v w
  rw [hgram, htensor] at h
  exact h


theorem GeneralizedStrongNeck.rescaled_eighth_flow_plane_lower
    (P : RicciFlowCurvatureTheory.{u})
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S)
    (v w : TangentSpace (𝓡 3) x) :
    -GeneralizedStrongNeck.rescaled_eighth_pinching_error S s hs x *
        M04.metricGram ((GeneralizedStrongNeck.rescaled_eighth_flow S H).metric s) x v w ≤
      ((GeneralizedStrongNeck.rescaled_eighth_flow S H).connection s).curvatureTensor x v w v w :=
  GeneralizedStrongNeck.rescaled_half_plane_lower_eighth_window S H P s hs x v w



theorem GeneralizedStrongNeck.rescaled_eighth_original_scalar_le_of_curvature_bound
    (P : RicciFlowCurvatureTheory.{u})
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S) {K : ℝ}
    (hcurv : ((GeneralizedStrongNeck.rescaled_eighth_flow S H).connection s).curvatureTensorNorm
      x ≤ K) :
    F.scalar (GeneralizedStrongNeck.rescaled_eighth_original_point S s hs x) ≤
      (9 * K) * (S.scale⁻¹ ^ 2) := by
  have hnorm := (GeneralizedStrongNeck.global_flow_curvature_eq_half_of_unit_scale
    S H (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos
    (GeneralizedStrongNeck.rescaled_secondary_scale_eq_one S) (1 / 8) (by norm_num)
    (GeneralizedStrongNeck.rescaled_eighth_global_window S) s x).2
  exact GeneralizedStrongNeck.global_original_scalar_le_of_curvature_bound
    S H (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos P (1 / 8) (by norm_num)
    (GeneralizedStrongNeck.rescaled_eighth_global_window S) s hs x (hnorm.trans_le hcurv)



theorem GeneralizedStrongNeck.rescaled_eighth_pinching_error_lt
    (P : RicciFlowCurvatureTheory.{u}) (hpinch : generalizedWeakHamiltonIveyPinched F)
    {K eta : ℝ} (hK : 0 ≤ K) (heta : 0 < eta)
    (hlarge : Real.exp (3 + (9 * K + 1) / (2 * eta)) / eta ≤ S.scale⁻¹ ^ 2)
    (s : ℝ) (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0) (x : strongNeckOpen S)
    (hcurv : ((GeneralizedStrongNeck.rescaled_eighth_flow S H).connection s).curvatureTensorNorm
      x ≤ K) :
    GeneralizedStrongNeck.rescaled_eighth_pinching_error S s hs x < eta := by
  let p := GeneralizedStrongNeck.rescaled_eighth_original_point S s hs x
  change (F.connection p.1).negativeCurvaturePart p.2 / (S.scale⁻¹ ^ 2) < eta
  apply (div_lt_iff₀ S.time_cylinder.scale_pos).mpr
  exact hpinch.negative_part_lt heta (by positivity) hlarge
    (GeneralizedStrongNeck.rescaled_eighth_original_point_time_mem S s hs x) p.2
    (GeneralizedStrongNeck.rescaled_eighth_original_scalar_le_of_curvature_bound
      S H P s hs x hcurv)



theorem strongNeck_eighth_pinching_error_eventually_lt
    (P : RicciFlowCurvatureTheory.{u}) {epsilon : ℝ}
    (F : ℕ → GeneralizedRicciFlowData.{u}) (t : ℕ → ℝ)
    (S : ∀ i, GeneralizedStrongNeck (F i) (t i) epsilon)
    (H : ∀ i, RescaledRawCylinderData (C := (F i).slice (t i))
      (U := strongNeckOpen (S i)) (J := strongNeckBackwardInterval)
      (strongNeckCylinder (S i)) (GeneralizedStrongNeck.physical_interval_subset (S i)))
    (hpinch : ∀ i, generalizedWeakHamiltonIveyPinched (F i))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ i s, s ∈ Icc (-(1 / 8 : ℝ)) 0 → ∀ x : strongNeckOpen (S i),
      ((GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i)).connection s).curvatureTensorNorm
        x ≤ K)
    (hQ : Tendsto (fun i => (S i).scale⁻¹ ^ 2) atTop atTop)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ i in atTop, ∀ s (hs : s ∈ Icc (-(1 / 8 : ℝ)) 0),
      ∀ x : strongNeckOpen (S i),
        GeneralizedStrongNeck.rescaled_eighth_pinching_error (S i) s hs x < eta := by
  filter_upwards [hQ.eventually_ge_atTop
    (Real.exp (3 + (9 * K + 1) / (2 * eta)) / eta)] with i hi
  intro s hs x
  exact GeneralizedStrongNeck.rescaled_eighth_pinching_error_lt
    (S i) (H i) P (hpinch i) hK heta hi s hs x (hcurv i s hs x)



theorem strongNeck_eighth_pinching_error_tendsto_zero
    (P : RicciFlowCurvatureTheory.{u}) {epsilon : ℝ}
    (F : ℕ → GeneralizedRicciFlowData.{u}) (t : ℕ → ℝ)
    (S : ∀ i, GeneralizedStrongNeck (F i) (t i) epsilon)
    (H : ∀ i, RescaledRawCylinderData (C := (F i).slice (t i))
      (U := strongNeckOpen (S i)) (J := strongNeckBackwardInterval)
      (strongNeckCylinder (S i)) (GeneralizedStrongNeck.physical_interval_subset (S i)))
    (hpinch : ∀ i, generalizedWeakHamiltonIveyPinched (F i))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ i s, s ∈ Icc (-(1 / 8 : ℝ)) 0 → ∀ x : strongNeckOpen (S i),
      ((GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i)).connection s).curvatureTensorNorm
        x ≤ K)
    (hQ : Tendsto (fun i => (S i).scale⁻¹ ^ 2) atTop atTop)
    (s : ℕ → ℝ) (hs : ∀ i, s i ∈ Icc (-(1 / 8 : ℝ)) 0)
    (x : ∀ i, strongNeckOpen (S i)) :
    Tendsto (fun i => GeneralizedStrongNeck.rescaled_eighth_pinching_error
      (S i) (s i) (hs i) (x i)) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le
      (GeneralizedStrongNeck.rescaled_eighth_pinching_error_nonneg (S i) (s i) (hs i) (x i))
  · intro eta heta
    exact (strongNeck_eighth_pinching_error_eventually_lt
      P F t S H hpinch hK hcurv hQ heta).mono fun i hi => hi (s i) (hs i) (x i)

end PoincareConjecture.M28
