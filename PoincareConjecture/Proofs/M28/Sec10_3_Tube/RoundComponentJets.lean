import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

theorem singularMetricJetErrorSquared_term_le
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X]
    (g₀ : RiemannianMetric 3 X) (D₀ : LeviCivitaData g₀)
    (B : CovariantTensorEvaluation 3 X 2) (k j : ℕ) (x : X)
    (hj : j ≤ k) {E : ℝ}
    (hE : singularMetricJetErrorSquared g₀ D₀ B k x ≤ E) :
    (g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
      (fun y v ↦ B y v - g₀.inner y (v 0) (v 1)) j) x) ^ 2 ≤ E := by
  unfold singularMetricJetErrorSquared at hE
  have hE' : ∑ i ∈ Finset.range k.succ,
      (g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
        (fun y v ↦ B y v - g₀.inner y (v 0) (v 1)) i) x) ^ 2 ≤ E := by
    simpa only [Nat.succ_eq_add_one] using hE
  have hsingle := Finset.single_le_sum
    (s := Finset.range k.succ)
    (f := fun i ↦ (g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
      (fun y v ↦ B y v - g₀.inner y (v 0) (v 1)) i) x) ^ 2)
    (fun i _ ↦ sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  exact hsingle.trans hE'

theorem singularMetricJetNorm_lt_of_error_lt
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X]
    (g₀ : RiemannianMetric 3 X) (D₀ : LeviCivitaData g₀)
    (B : CovariantTensorEvaluation 3 X 2) (k j : ℕ) (x : X)
    (hj : j ≤ k) {epsilon E : ℝ} (hepsilon : 0 < epsilon)
    (hE : singularMetricJetErrorSquared g₀ D₀ B k x ≤ E)
    (hEepsilon : E < epsilon ^ 2) :
    g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
      (fun y v ↦ B y v - g₀.inner y (v 0) (v 1)) j) x < epsilon := by
  have hsq := singularMetricJetErrorSquared_term_le g₀ D₀ B k j x hj hE
  have hlt : (g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
      (fun y v ↦ B y v - g₀.inner y (v 0) (v 1)) j) x) ^ 2 < epsilon ^ 2 :=
    hsq.trans_lt hEepsilon
  have hnorm : 0 ≤ g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
      (fun y v ↦ B y v - g₀.inner y (v 0) (v 1)) j) x := by
    exact Real.sqrt_nonneg _
  nlinarith

end PoincareConjecture
