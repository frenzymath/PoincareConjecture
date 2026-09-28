import PoincareConjecture.Proofs.M45.AnalyticCalibration
import PoincareConjecture.Statements.Ch04.CurvatureTheory










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem M45PointwiseAnalyticEstimate.mono
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {x : M} {B B' : ℝ}
    (h : M45PointwiseAnalyticEstimate g D x B) (hB : B ≤ B') :
    M45PointwiseAnalyticEstimate g D x B' := by
  exact ⟨h.1,
    h.2.1.trans (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg h.1.le _)),
    h.2.2.trans (mul_le_mul_of_nonneg_right hB (sq_nonneg _))⟩

namespace RepairedControlledSchedulesData

variable (S : RepairedControlledSchedulesData.{u})


noncomputable def modelAnalyticBound : ℝ :=
  max 1 (max S.calibration.Ckappa (max S.calibration.Cstandard
    (max S.calibration.model_analytics.neck_constant
      S.calibration.model_analytics.round_constant)))

noncomputable def modelAnalyticConstant : ℝ := 2 * S.modelAnalyticBound

theorem one_le_modelAnalyticBound : 1 ≤ S.modelAnalyticBound := le_max_left _ _

theorem modelAnalyticBound_pos : 0 < S.modelAnalyticBound :=
  zero_lt_one.trans_le S.one_le_modelAnalyticBound

theorem kappa_le_modelAnalyticBound : S.calibration.Ckappa ≤ S.modelAnalyticBound :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem standard_le_modelAnalyticBound :
    S.calibration.Cstandard ≤ S.modelAnalyticBound :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem neck_le_modelAnalyticBound :
    S.calibration.model_analytics.neck_constant ≤ S.modelAnalyticBound :=
  (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem round_le_modelAnalyticBound :
    S.calibration.model_analytics.round_constant ≤ S.modelAnalyticBound :=
  (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem modelAnalyticConstant_pos : 0 < S.modelAnalyticConstant :=
  mul_pos (by norm_num) S.modelAnalyticBound_pos

theorem modelAnalyticConstant_half : S.modelAnalyticConstant / 2 = S.modelAnalyticBound := by
  unfold modelAnalyticConstant
  ring

theorem modelAnalyticBound_lt_constant : S.modelAnalyticBound < S.modelAnalyticConstant := by
  unfold modelAnalyticConstant
  linarith [S.modelAnalyticBound_pos]


noncomputable def calibrateModelAnalytics : RepairedControlledSchedulesData.{u} :=
  S.recalibrateAnalytic S.modelAnalyticConstant S.modelAnalyticConstant_pos

theorem calibrateModelAnalytics_constant :
    S.calibrateModelAnalytics.calibration.analytic_constant = S.modelAnalyticConstant := rfl

theorem calibrateModelAnalytics_modelBound :
    S.calibrateModelAnalytics.modelAnalyticBound = S.modelAnalyticBound := rfl

theorem calibrateModelAnalytics_models :
    S.calibrateModelAnalytics.calibration.model_analytics = S.calibration.model_analytics := rfl

section GeometricModels

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem neckModelAnalytics (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (N : EpsilonNeck g) (hepsilon : N.epsilon ≤ 1 / 200) :
    M45PointwiseAnalyticEstimate g D N.center S.modelAnalyticBound :=
  (S.calibration.model_analytics.neck g D N hepsilon).mono S.neck_le_modelAnalyticBound

theorem roundModelAnalytics (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (epsilon : ℝ) (N : SingularRoundComponent g epsilon)
    (hepsilon : epsilon ≤ 1 / 200) (x : M) (hx : x ∈ N.carrier) :
    M45PointwiseAnalyticEstimate g D x S.modelAnalyticBound :=
  (S.calibration.model_analytics.round g D epsilon N hepsilon x hx).mono
    S.round_le_modelAnalyticBound

end GeometricModels

section Ancient

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem kappaModelAnalytics (h04 : RicciFlowCurvatureTheory.{u})
    (K : AncientKappaSolution 3 M) (t : ℝ) (ht : t ≤ 0) (x : M) :
    M45PointwiseAnalyticEstimate (K.flow.metric t) (K.flow.connection t) x
      S.modelAnalyticBound := by
  obtain ⟨B, _, hB, h⟩ := S.calibration.kappa_derivatives K
  obtain ⟨hR, hgrad, d, hd, htime⟩ := h t ht x
  have hevolution := h04.scalar_evolution 3 M (Set.Iic 0) K.flow t ht x
  have hd_eq := (uniqueDiffOn_Iic (0 : ℝ) t ht).eq_deriv (Set.Iic 0) hd hevolution
  rw [hd_eq] at htime
  exact (show M45PointwiseAnalyticEstimate (K.flow.metric t) (K.flow.connection t) x B
    from ⟨hR, hgrad, htime⟩).mono (hB.le.trans S.kappa_le_modelAnalyticBound)

end Ancient


theorem standardModelAnalytics (t : ℝ)
    (ht : t ∈ Set.Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime)
    (x : StandardCapSpace) :
    M45PointwiseAnalyticEstimate (S.cap_persistence.standard_cap.flow.metric t)
      (S.cap_persistence.standard_cap.flow.connection t) x S.modelAnalyticBound := by
  have hepsilon : S.calibration.beta * S.setup.epsilon / 3 ≤ 1 / 200 := by
    have hbase : S.setup.epsilon ≤ 1 / 200 :=
      S.calibration.epsilon_source_le.trans (min_le_left _ _)
    have hbeta := S.calibration.beta_lt_half
    have heps := S.setup.epsilon_pos
    nlinarith
  cases S.calibration.canonical_source t ht x with
  | cap N =>
    have hxcore : x ∈ N.closed_core := interior_subset N.center_in_core
    rw [N.closed_core_eq] at hxcore
    have hx : x ∈ N.carrier := hxcore.1
    exact (show M45PointwiseAnalyticEstimate _ _ x S.calibration.Cstandard from
      ⟨N.scalar_pos x hx, (N.gradient_bound x hx).le,
        (N.time_derivative_bound x hx).le⟩).mono S.standard_le_modelAnalyticBound
  | initial_neck N _ =>
    have hzero : (0 : ℝ) ∈ Set.Icc
        (-t * (S.cap_persistence.standard_cap.flow.connection t).scalarCurvature x) 0 :=
      ⟨mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) N.scalar_pos.le, le_rfl⟩
    exact (S.calibration.model_analytics.standard_neck _ _ _ _ _ _ N hepsilon hzero).mono
      S.neck_le_modelAnalyticBound
  | evolving_neck N =>
    have hzero : (0 : ℝ) ∈ Set.Ioc (-(1 + S.calibration.beta * S.setup.epsilon / 3)) 0 := by
      have heps := N.epsilon_pos
      constructor <;> linarith
    exact (S.calibration.model_analytics.standard_neck _ _ _ _ _ _ N hepsilon hzero).mono
      S.neck_le_modelAnalyticBound

end RepairedControlledSchedulesData

end PoincareConjecture
