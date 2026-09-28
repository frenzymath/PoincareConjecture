import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M45.Ch9_Models.ModelAnalyticBounds
import PoincareConjecture.Definitions.Ch15.SurgeryFlow










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47




theorem exists_jointSeed_ordinary_analytic_bound (C : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ C ≤ A ∧
      ∀ (S : GeneralizedSliceCarrier.{u}) [ConnectedSpace S.carrier]
        (J : Set ℝ) (F : RicciFlow 3 S.carrier J) (t epsilon : ℝ),
        epsilon ≤ 1 / 200 → ∀ p q : S.carrier,
        (C / 6) * (F.connection t).scalarCurvature p ≤
          (F.connection t).scalarCurvature q →
        SurgeryOrdinaryCanonicalControl S F t q epsilon C →
        M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) q A := by
  let B := M45.modelAnalyticBounds.{u}
  let A := max 1 (max C (max B.neck_constant B.round_constant))
  have hC : C ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hneck : B.neck_constant ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hround : B.round_constant ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨A, le_max_left _ _, hC, ?_⟩
  intro S _ J F t epsilon hepsilon p q hgap hcanonical
  have hmono {a : ℝ} (ha : a ≤ A)
      (h : M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) q a) :
      M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) q A :=
    ⟨h.1,
      h.2.1.trans (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg h.1.le _)),
      h.2.2.trans (mul_le_mul_of_nonneg_right ha (sq_nonneg _))⟩
  cases hcanonical with
  | neck N hcenter =>
      have h := B.neck (F.metric t) (F.connection t) N.neck
        (N.epsilon_eq.le.trans hepsilon)
      rw [hcenter] at h
      exact hmono hneck h
  | cap N _ hconstant hconnection hqcore =>
      have hqcarrier : q ∈ N.carrier := by
        rw [N.core_eq_interior_closed_core] at hqcore
        have hclosed := interior_subset hqcore
        rw [N.closed_core_eq_complement_end] at hclosed
        exact hclosed.1
      have hR := N.scalar_pos q hqcarrier
      obtain ⟨Bgrad, hBgrad, hgrad⟩ := N.gradient_bound
      obtain ⟨Bevol, hBevol, hevol⟩ := N.laplacian_bound
      have hg := hgrad q hqcarrier
      have he := hevol q hqcarrier
      rw [hconnection] at hR hg he
      exact ⟨hR,
        hg.trans (mul_le_mul_of_nonneg_right
          ((hBgrad.le.trans hconstant).trans hC) (Real.rpow_nonneg hR.le _)),
        he.trans (mul_le_mul_of_nonneg_right
          ((hBevol.le.trans hconstant).trans hC) (sq_nonneg _))⟩
  | component N hqcarrier =>
      have hp : p ∈ N.carrier := by
        rw [N.component_eq, PreconnectedSpace.connectedComponent_eq_univ]
        trivial
      exact (not_lt_of_ge hgap (component_scalar_ratio N hp hqcarrier)).elim
  | round N hqcarrier =>
      exact hmono hround (B.round (F.metric t) (F.connection t)
        epsilon N hepsilon q hqcarrier)

end PoincareConjecture.M47
