import PoincareConjecture.Proofs.M47.LimitCanonicalTensorMargin
import PoincareConjecture.Definitions.M27CanonicalGeometry

set_option autoImplicit false

set_option linter.style.haveILetI false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem limitCanonical_covariant_sub_metric
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {B : CovariantTensorEvaluation 3 M 2} (hB : IsSmoothCovariantTensor B) :
    D.covariantTensorDerivative (fun y v => B y v - g.inner y (v 0) (v 1)) =
      D.covariantTensorDerivative B := by
  have hsub := D.covariantTensorDerivative_sub hB
    (M44.isSmoothCovariantTensor_metric g)
  funext x v
  rw [hsub]
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  change D.covariantTensorDerivative B x ![v 0, v 1, v 2] -
      D.covariantTensorDerivative (fun y w => g.inner y (w 0) (w 1)) x
        ![v 0, v 1, v 2] = _
  rw [D.covariantTensorDerivative_metric_eq_zero]
  simp

theorem limitCanonical_iterated_sub_metric
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {B : CovariantTensorEvaluation 3 M 2} (hB : IsSmoothCovariantTensor B)
    (j : ℕ) (hj : 0 < j) :
    D.iteratedCovariantTensorDerivative
        (fun y v => B y v - g.inner y (v 0) (v 1)) j =
      D.iteratedCovariantTensorDerivative B j := by
  cases j with
  | zero => omega
  | succ j =>
    induction j with
    | zero =>
        change D.covariantTensorDerivative
            (fun y v => B y v - g.inner y (v 0) (v 1)) =
          D.covariantTensorDerivative B
        exact limitCanonical_covariant_sub_metric D hB
    | succ j ih =>
        change D.covariantTensorDerivative
            (D.iteratedCovariantTensorDerivative
              (fun y v => B y v - g.inner y (v 0) (v 1)) (j + 1)) =
          D.covariantTensorDerivative
            (D.iteratedCovariantTensorDerivative B (j + 1))
        rw [ih (by omega)]

theorem limitCanonical_singularMetricJetErrorSquared_eq
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {B : CovariantTensorEvaluation 3 M 2} (hB : IsSmoothCovariantTensor B)
    (m : ℕ) (x : M) :
    singularMetricJetErrorSquared g D B m x =
      g.tensorNorm (fun y v => B y v - g.inner y (v 0) (v 1)) x ^ 2 +
        ∑ j ∈ Finset.range m,
          g.tensorNorm (D.iteratedCovariantTensorDerivative B (j + 1)) x ^ 2 := by
  unfold singularMetricJetErrorSquared
  rw [Finset.sum_range_succ']
  have hshift :
      (∑ k ∈ Finset.range m,
        g.tensorNorm (D.iteratedCovariantTensorDerivative
          (fun y v => B y v - g.inner y (v 0) (v 1)) (k + 1)) x ^ 2) =
      ∑ k ∈ Finset.range m,
        g.tensorNorm (D.iteratedCovariantTensorDerivative B (k + 1)) x ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [limitCanonical_iterated_sub_metric D hB (k + 1) (by omega)]
  rw [hshift]
  have hzero : D.iteratedCovariantTensorDerivative
      (fun y v => B y v - g.inner y (v 0) (v 1)) 0 =
      (fun y v => B y v - g.inner y (v 0) (v 1)) := rfl
  rw [hzero, add_comm]

section Round

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem limitCanonical_round_error_lt
    {K : AncientKappaSolution 3 M} {t epsilon : ℝ}
    (N : M27EpsilonRoundComponent K t epsilon) :
    ∀ z : N.reference,
      letI : TopologicalSpace N.reference := N.reference_topology
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N.reference := N.reference_charted
      letI : IsManifold (𝓡 3) ∞ N.reference := N.reference_manifold
      singularMetricJetErrorSquared N.reference_metric N.reference_connection
          (m27RescaledPullbackMetric (K.flow.metric t) N.scale N.identification)
          (Nat.floor epsilon⁻¹) z < epsilon ^ 2 := by
  letI : TopologicalSpace N.reference := N.reference_topology
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N.reference := N.reference_charted
  letI : IsManifold (𝓡 3) ∞ N.reference := N.reference_manifold
  let B : CovariantTensorEvaluation 3 N.reference 2 :=
    m27RescaledPullbackMetric (K.flow.metric t) N.scale N.identification
  have hB : IsSmoothCovariantTensor B := by
    exact (M44.isSmoothCovariantTensor_metric_pullback
      (K.flow.metric t) N.identification.contMDiff).const_mul N.scale
  obtain ⟨C, hC, hbound⟩ := N.comparison
  intro z
  rw [limitCanonical_singularMetricJetErrorSquared_eq
    N.reference_connection hB]
  exact (hbound z).trans_lt hC

end Round

end PoincareConjecture.M47
