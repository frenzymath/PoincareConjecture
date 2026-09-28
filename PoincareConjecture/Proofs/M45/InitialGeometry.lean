import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Proofs.M01.NormalizationVolume









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SurgeryFlowData


theorem initialVolume_eq (F : SurgeryFlowData.{u}) :
    calibratedMetricVolume (F.metric 0) = normalizedMetricVolume (F.metric 0) := rfl


noncomputable def normalizedInitialData (F : SurgeryFlowData.{u}) :
    NormalizedInitialMetric (M := (F.slice 0).carrier) := by
  letI : CompactSpace (F.slice 0).carrier :=
    isCompact_univ_iff.mp (F.slices_compact 0 F.zero_mem)
  refine ⟨F.metric 0, F.connection 0, calibratedMetricVolume (F.metric 0),
    F.initialVolume_eq, fun x => (F.initial_normalized x).1, ?_, ?_, ?_⟩
  · intro x r hr hr1
    have hfinite : euclideanUnitBallLebesgueVolume ≠ ⊤ :=
      Metric.isBounded_ball.measure_lt_top.ne
    have hcoeff : ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) =
        (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfinite,
        ENNReal.ofReal_pow hr.le]
      norm_num only [ENNReal.ofReal_ofNat]
      simp only [div_eq_mul_inv, mul_right_comm]
    rw [← hcoeff]
    exact (F.initial_normalized x).2 r hr hr1
  · rw [F.initialVolume_eq]
    exact m01_normalizedMetricVolume_finite (F.metric 0)
  · unfold normalizedMetricComplete
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (F.slice 0).carrier → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : (F.slice 0).carrier → Type _) :=
      ⟨⟨(F.metric 0).inner, (F.metric 0).toContinuousRiemannianMetric.continuous,
        fun _ _ _ => rfl⟩⟩
    let : EMetricSpace (F.slice 0).carrier :=
      EMetricSpace.ofRiemannianMetric (𝓡 3) (F.slice 0).carrier
    exact complete_of_compact

end SurgeryFlowData

namespace RepairedControlledSchedulesData


theorem initialOrdinaryFlow (S : RepairedControlledSchedulesData.{u})
    (F : SurgeryFlowData.{u}) :
    ∃ G : RicciFlow 3 (F.slice 0).carrier (Set.Icc 0 (1 / 16 : ℝ)),
      G.metric 0 = F.metric 0 ∧ HEq (G.connection 0) (F.connection 0) ∧
      (∀ t ∈ Set.Icc 0 (1 / 16 : ℝ), ∀ x : (F.slice 0).carrier,
        (G.connection t).curvatureTensorNorm x ≤ 2) ∧
      (∀ t ∈ Set.Icc 0 (1 / 16 : ℝ), ∀ x : (F.slice 0).carrier, ∀ r : ℝ,
        0 < r → r ≤ S.setup.epsilon →
          ENNReal.ofReal (S.kappa0 * r ^ 3) ≤
            calibratedMetricVolume (G.metric t) ((G.metric t).ball x r)) := by
  let : CompactSpace (F.slice 0).carrier :=
    isCompact_univ_iff.mp (F.slices_compact 0 F.zero_mem)
  exact S.calibration.claim151 F.normalizedInitialData


theorem initialFrontier_lt (S : RepairedControlledSchedulesData.{u})
    (F : SurgeryFlowData.{u}) (H : ℝ) (hH : 0 < H)
    (hDomain : F.time_domain = Set.Ico 0 H) : 1 / 16 < H := by
  by_contra h
  have hHle : H ≤ 1 / 16 := le_of_not_gt h
  have hJ : Set.Ico 0 H ⊆ F.time_domain := by rw [hDomain]
  have hSubset : Set.Ioo 0 H ⊆ Set.Icc 0 (1 / 16 : ℝ) :=
    fun _ ht => ⟨ht.1.le, ht.2.le.trans hHle⟩
  have hNo : Disjoint F.surgery_times (Set.Ioo 0 H) :=
    (S.calibration.initial_capture F).1.mono_right hSubset
  let : Nonempty (F.slice 0).carrier := F.initial_nonempty
  have hEnd : H ∉ F.time_domain := by simp [hDomain]
  obtain ⟨t, ht, x, hx⟩ :=
    F.maximal_intervals 0 H F.zero_mem (Or.inl rfl) hH hJ hNo
      (Or.inr hEnd) 2 0 hH
  have ht0 : 0 < t := by simpa using ht.1
  have hBound := ((S.calibration.initial_capture F).2 t
    (hJ ⟨ht0.le, ht.2⟩) (ht.2.le.trans hHle) x).1
  exact (not_lt_of_ge hBound) hx


theorem initialAnalyticControl (S : RepairedControlledSchedulesData.{u})
    (F : SurgeryFlowData.{u}) (A : ℝ) :
    SurgeryHighCurvatureAnalyticOn F (Set.Icc 0 (1 / 16 : ℝ))
      (S.setup.epsilon / 2) A := by
  intro t ht hDomain x hCurv
  have hScalar := ((S.calibration.initial_capture F).2 t hDomain ht.2 x).2.1
  have hEps := S.setup.epsilon_le.trans (min_le_left _ _)
  have hInv : 400 ≤ (S.setup.epsilon / 2)⁻¹ := by
    have h := one_div_le_one_div_of_le (half_pos S.setup.epsilon_pos)
      (show S.setup.epsilon / 2 ≤ (1 : ℝ) / 400 by linarith)
    norm_num [one_div] at h
    simpa only [inv_div] using h
  exfalso
  nlinarith [le_abs_self ((F.connection t).scalarCurvature x)]

end RepairedControlledSchedulesData

end PoincareConjecture
