import PoincareConjecture.Proofs.M47.BlowupControlsComponent
import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Definitions.M47ComponentAnalytics

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

noncomputable def blowupAnalyticConstant (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) : ℝ :=
  max 1 (max (2 * S.setup.C) (max S.calibration.model_analytics.neck_constant
    (max S.calibration.model_analytics.round_constant B.constant)))

theorem blowupAnalyticConstant_pos (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) : 0 < blowupAnalyticConstant S B :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem canonical_blowup_analytic_estimate
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) (F : SurgeryFlowData.{u})
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    (t Q : ℝ) (x : (F.slice t).carrier)
    (hQ : (F.connection t).scalarCurvature x = Q)
    (hLarge : B.curvature_threshold ≤ Q)
    (hDomain : Icc (t - B.duration / Q) t ⊆ F.time_domain)
    (hPinched : ∀ s ∈ Icc (t - B.duration / Q) t,
      SurgeryPinchedAt (F.connection s) s)
    (hEarlier : ∀ s ∈ Ico (t - B.duration / Q) t, ∀ y : (F.slice s).carrier,
      Q ≤ (F.connection s).scalarCurvature y →
        SurgeryCanonicalControl F s y F.parameters.epsilon S.setup.C)
    (hDelta : ∀ T ∈ Icc (t - B.duration / Q) t, T ∈ F.surgery_times →
      F.parameters.delta T ≤ B.delta S.setup.standard_initial S.constants)
    {epsilon C : ℝ} (hEpsilon : epsilon ≤ 1 / 200) (hConstant : C ≤ 2 * S.setup.C)
    (hCanonical : SurgeryCanonicalControl F t x epsilon C) :
    M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x
      (blowupAnalyticConstant S B) := by
  have hCap : C ≤ blowupAnalyticConstant S B :=
    hConstant.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hNeck : S.calibration.model_analytics.neck_constant ≤ blowupAnalyticConstant S B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hRound : S.calibration.model_analytics.round_constant ≤
      blowupAnalyticConstant S B :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hComponent : B.constant ≤ blowupAnalyticConstant S B :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have mono {a : ℝ} (ha : a ≤ blowupAnalyticConstant S B)
      (h : M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x a) :
      M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x
        (blowupAnalyticConstant S B) :=
    ⟨h.1,
      h.2.1.trans (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg h.1.le _)),
      h.2.2.trans (mul_le_mul_of_nonneg_right ha (sq_nonneg _))⟩
  cases hCanonical with
  | neck N hcenter =>
      have h := S.calibration.model_analytics.neck (F.metric t) (F.connection t)
        N.neck (N.epsilon_eq.le.trans hEpsilon)
      rw [hcenter] at h
      exact mono hNeck h
  | cap N _ hconstant hconnection hx =>
      have hxcarrier : x ∈ N.carrier := by
        rw [N.core_eq_interior_closed_core] at hx
        have hclosed := interior_subset hx
        rw [N.closed_core_eq_complement_end] at hclosed
        exact hclosed.1
      have hR := N.scalar_pos x hxcarrier
      obtain ⟨Bgrad, hBgrad, hgrad⟩ := N.gradient_bound
      obtain ⟨Bevol, hBevol, hevol⟩ := N.laplacian_bound
      have hg := hgrad x hxcarrier
      have he := hevol x hxcarrier
      rw [hconnection] at hR hg he
      exact ⟨hR,
        hg.trans (mul_le_mul_of_nonneg_right
          ((hBgrad.le.trans hconstant).trans hCap) (Real.rpow_nonneg hR.le _)),
        he.trans (mul_le_mul_of_nonneg_right
          ((hBevol.le.trans hconstant).trans hCap) (sq_nonneg _))⟩
  | component N hx =>
      exact mono hComponent
        (B.estimate S.setup.standard_initial S.constants F hInitial hConstants hC
          F.parameters.epsilon_le t Q x hQ hLarge hDomain hPinched hEarlier hDelta
          (component_relax_constant N hConstant) hx)
  | round N hx =>
      exact mono hRound (S.calibration.model_analytics.round
        (F.metric t) (F.connection t) epsilon N hEpsilon x hx)

end PoincareConjecture.M47
