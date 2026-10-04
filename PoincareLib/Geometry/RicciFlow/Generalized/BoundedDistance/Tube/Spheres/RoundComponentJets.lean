import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry

/-!
# Finite jet consequences of a round-component comparison

The frozen round-component comparison is a squared finite covariant-jet
bound. This file exposes each individual nonnegative jet term, and hence
its strict norm bound, without assuming that a chosen model chart varies
continuously with the model point. The curvature/scalar transfer from
these finite jets is a separate producer.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT

/-- Each retained nonnegative summand of the frozen squared jet error is
bounded by its total comparison error (Definition 2.16 and Definition
9.76; section 10.3.1, p. 247). -/
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

/-- A strict squared comparison gives a strict bound on every retained
jet norm (Definition 9.76; task derivation 16). -/
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

end PoincareMT
