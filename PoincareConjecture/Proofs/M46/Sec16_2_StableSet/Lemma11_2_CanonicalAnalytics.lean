import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46



noncomputable def seedAnalyticConstant (S : RepairedControlledSchedulesData.{u}) : ℝ :=
  max S.setup.C (max S.calibration.model_analytics.neck_constant
    S.calibration.model_analytics.round_constant)


theorem seedAnalyticConstant_pos (S : RepairedControlledSchedulesData.{u}) :
    0 < seedAnalyticConstant S :=
  S.setup.C_pos.trans_le (le_max_left _ _)




theorem canonical_analytic_on_nonpositive (S : RepairedControlledSchedulesData.{u})
    (F : SurgeryFlowData.{u}) (t : ℝ) (x : (F.slice t).carrier)
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon S.setup.C)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x) :
    M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x
      (seedAnalyticConstant S) := by
  have hC : S.setup.C ≤ seedAnalyticConstant S := le_max_left _ _
  have hneck : S.calibration.model_analytics.neck_constant ≤ seedAnalyticConstant S :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hround : S.calibration.model_analytics.round_constant ≤ seedAnalyticConstant S :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hmono {B : ℝ} (hB : B ≤ seedAnalyticConstant S)
      (h : M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x B) :
      M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x
        (seedAnalyticConstant S) :=
    ⟨h.1,
      h.2.1.trans (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg h.1.le _)),
      h.2.2.trans (mul_le_mul_of_nonneg_right hB (sq_nonneg _))⟩
  cases hcanonical with
  | neck N hcenter =>
      have hsmall : N.neck.epsilon ≤ 1 / 200 :=
        N.epsilon_eq.le.trans F.parameters.epsilon_le
      have h := S.calibration.model_analytics.neck (F.metric t) (F.connection t)
        N.neck hsmall
      rw [hcenter] at h
      exact hmono hneck h
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
          ((hBgrad.le.trans hconstant).trans hC) (Real.rpow_nonneg hR.le _)),
        he.trans (mul_le_mul_of_nonneg_right
          ((hBevol.le.trans hconstant).trans hC) (sq_nonneg _))⟩
  | component N hx =>
      have hxcomponent : x ∈ connectedComponent N.basepoint := by
        rwa [← N.component_eq]
      have hcomponent : connectedComponent x = N.carrier :=
        (connectedComponent_eq hxcomponent).symm.trans N.component_eq.symm
      exact (hpositive (by
        intro y hy v w hvw
        exact N.positive_sectional y (hcomponent ▸ hy) v w hvw)).elim
  | round N hx =>
      exact hmono hround
        (S.calibration.model_analytics.round (F.metric t) (F.connection t)
          F.parameters.epsilon N F.parameters.epsilon_le x hx)



theorem old_prefix_analytic_on_nonpositive (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) {t : ℝ}
    (ht : t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i)
    (x : (F.slice t).carrier) (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hscalar : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x) :
    M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x
      (seedAnalyticConstant S) := by
  have hcanonical := old.canonical (Fin.last p.i) (by simp) t ht
    (O.interval_subset ht.1) x hscalar
  rw [old.C_eq, compatible.setup_eq] at hcanonical
  exact canonical_analytic_on_nonpositive S F t x hcanonical hpositive

end PoincareConjecture.Proofs.M46
