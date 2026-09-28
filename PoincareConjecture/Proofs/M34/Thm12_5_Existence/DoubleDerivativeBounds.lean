import PoincareConjecture.Proofs.M34.Standard.CompactDerivativeBounds
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleFlows











set_option autoImplicit false

open scoped Manifold ContDiff
open Set

namespace PoincareConjecture.M34



theorem endDouble_initialDerivative_bounds_upto (g0 : StandardInitialMetric)
    (E0 : StandardCapEstimate g0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 < L)
      (D : LeviCivitaData (endDoubleMetric g0.cylindrical_end hL)),
      ∀ j ≤ k, ∀ q : EndDouble g0.cylindrical_end hL, D.curvatureDerivativeNorm j q ≤ C := by
  induction k with
  | zero =>
      obtain ⟨C, hC, hb⟩ := endDouble_curvatureDerivative_bounds g0 E0 0
      refine ⟨C, hC, fun L hL D j hj q => ?_⟩
      have hj0 : j = 0 := by omega
      subst j
      exact hb L hL D q
  | succ k ih =>
      obtain ⟨C, hC, hb⟩ := ih
      obtain ⟨A, hA, ha⟩ := endDouble_curvatureDerivative_bounds g0 E0 (k + 1)
      refine ⟨max C A, le_max_of_le_left hC, fun L hL D j hj q => ?_⟩
      by_cases hjk : j ≤ k
      · exact (hb L hL D j hjk q).trans (le_max_left _ _)
      · have hjs : j = k + 1 := by omega
        subst j
        exact (ha L hL D q).trans (le_max_right _ _)



theorem endDouble_flow_curvatureDerivative_bounds (P : RicciFlowCurvatureTheory.{0})
    (g0 : StandardInitialMetric) (E0 : StandardCapEstimate g0)
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (hL : 1 < L)
      (F : RicciFlow 3 (EndDouble g0.cylindrical_end hL) (Icc 0 T)),
      F.metric 0 = endDoubleMetric g0.cylindrical_end hL →
      (∀ t ∈ Icc 0 T, ∀ q : EndDouble g0.cylindrical_end hL,
        (F.connection t).curvatureTensorNorm q ≤ B) →
      ∀ t ∈ Icc 0 T, ∀ q : EndDouble g0.cylindrical_end hL,
        (F.connection t).curvatureDerivativeNorm k q ≤ C := by
  obtain ⟨A, _hA, hA⟩ := endDouble_initialDerivative_bounds_upto g0 E0 k
  have hK : 0 < max B A := hB.trans_le (le_max_left _ _)
  obtain ⟨C, hC, hest⟩ := compact_initial_derivative_bound P 3 k hK hT
  refine ⟨C, hC, fun L hL F hF hfull => ?_⟩
  apply hest (EndDouble g0.cylindrical_end hL) F
  · exact fun t ht q => (hfull t ht q).trans (le_max_left _ _)
  · have hinit : ∀ D : LeviCivitaData (F.metric 0), ∀ j ≤ k,
        ∀ q : EndDouble g0.cylindrical_end hL, D.curvatureDerivativeNorm j q ≤ A := by
      rw [hF]
      exact hA L hL
    exact fun j hj q => (hinit (F.connection 0) j hj q).trans (le_max_right _ _)

end PoincareConjecture.M34
