import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M45.Ch9_Models.ModelAnalyticBounds
import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

theorem exists_component_crossing_analytic_bound (C : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (F : SurgeryFlowData.{u}) (t : ℝ) (p q z : (F.slice t).carrier),
        q ∈ connectedComponent p → z ∈ connectedComponent p →
        (C / 6) * (F.connection t).scalarCurvature q ≤
          (F.connection t).scalarCurvature p →
        SurgeryCanonicalControl F t z F.parameters.epsilon C →
        M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) z B := by
  let A := M45.modelAnalyticBounds.{u}
  let B := max 1 (max C (max A.neck_constant A.round_constant))
  have hC : C ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hneck : A.neck_constant ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hround : A.round_constant ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨B, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _), ?_⟩
  intro F t p q z hq hz hgap hcanonical
  have hmono {a : ℝ} (ha : a ≤ B)
      (h : M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) z a) :
      M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) z B :=
    ⟨h.1,
      h.2.1.trans (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg h.1.le _)),
      h.2.2.trans (mul_le_mul_of_nonneg_right ha (sq_nonneg _))⟩
  cases hcanonical with
  | neck N hcenter =>
      have h := A.neck (F.metric t) (F.connection t) N.neck
        (N.epsilon_eq.le.trans F.parameters.epsilon_le)
      rw [hcenter] at h
      exact hmono hneck h
  | cap N _ hconstant hconnection hzcore =>
      have hzcarrier : z ∈ N.carrier := by
        rw [N.core_eq_interior_closed_core] at hzcore
        have hclosed := interior_subset hzcore
        rw [N.closed_core_eq_complement_end] at hclosed
        exact hclosed.1
      have hR := N.scalar_pos z hzcarrier
      obtain ⟨Bgrad, hBgrad, hgrad⟩ := N.gradient_bound
      obtain ⟨Bevol, hBevol, hevol⟩ := N.laplacian_bound
      have hg := hgrad z hzcarrier
      have he := hevol z hzcarrier
      rw [hconnection] at hR hg he
      exact ⟨hR,
        hg.trans (mul_le_mul_of_nonneg_right
          ((hBgrad.le.trans hconstant).trans hC) (Real.rpow_nonneg hR.le _)),
        he.trans (mul_le_mul_of_nonneg_right
          ((hBevol.le.trans hconstant).trans hC) (sq_nonneg _))⟩
  | component N hzcarrier =>
      have hzbase : z ∈ connectedComponent N.basepoint := by
        rwa [← N.component_eq]
      have hcomponent : N.carrier = connectedComponent p :=
        N.component_eq.trans ((connectedComponent_eq hzbase).trans
          (connectedComponent_eq hz).symm)
      have hpN : p ∈ N.carrier := hcomponent.symm ▸ mem_connectedComponent
      have hqN : q ∈ N.carrier := hcomponent.symm ▸ hq
      exact (not_lt_of_ge hgap (component_scalar_ratio N hqN hpN)).elim
  | round N hzcarrier =>
      exact hmono hround (A.round (F.metric t) (F.connection t)
        F.parameters.epsilon N F.parameters.epsilon_le z hzcarrier)

end PoincareConjecture.M47
