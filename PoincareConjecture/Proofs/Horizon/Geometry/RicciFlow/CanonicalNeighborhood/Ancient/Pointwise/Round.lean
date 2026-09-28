import PoincareConjecture.Definitions.M27CanonicalGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.RoundQuotient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TimeShift
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareConjecture

private theorem round_iterated_metric_derivative_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (j : ℕ) :
    D.iteratedCovariantTensorDerivative (k := 2) (fun y a => g.inner y (a 0) (a 1)) (j + 1) =
      fun _ _ => 0 := by
  induction j with
  | zero =>
    funext x a
    have ha : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
    rw [ha]
    exact D.covariantTensorDerivative_metric_eq_zero x (a 0) (a 1) (a 2)
  | succ j ih =>
    rw [LeviCivitaData.iteratedCovariantTensorDerivative, ih]
    funext x a
    simp [LeviCivitaData.covariantTensorDerivative, mvfderiv_const]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem epsilonRoundComponent_of_roundSlice
    (K : AncientKappaSolution 3 M) {t epsilon : ℝ} (ht : t ≤ 0)
    (hepsilon : 0 < epsilon) (hround : IsRoundMetricSlice (K.flow.connection t)) :
    Nonempty (M27EpsilonRoundComponent K t epsilon) := by
  let : CompactSpace M := AncientKappaRoundness.compactSpace_of_isRoundMetricSlice
    (K.flow.connection t) (K.complete t ht) hround
  obtain ⟨c, hc, hsec⟩ := compactRound_sectionalCurvature hround
  let g := rescaledMetric (K.flow.metric t) c hc
  let D := rescaledMetric_connection (K.flow.metric t) (K.flow.connection t) c hc
  have hmetric : m27RescaledPullbackMetric (K.flow.metric t) c
      (Diffeomorph.refl (𝓡 3) M ∞) = fun y a => g.inner y (a 0) (a 1) := by
    funext y a
    simp [m27RescaledPullbackMetric, g, rescaledMetric_inner]
  refine ⟨{
    time_mem := ht
    epsilon_pos := hepsilon
    compact := isCompact_univ
    reference := M
    reference_topology := inferInstance
    reference_charted := inferInstance
    reference_manifold := inferInstance
    reference_compact := isCompact_univ
    reference_connected := inferInstance
    reference_metric := g
    reference_connection := D
    reference_sectional_one := ?_
    scale := c
    scale_pos := hc
    identification := Diffeomorph.refl (𝓡 3) M ∞
    comparison := ?_
  }⟩
  · intro y a b ha hb hab
    have hgram : (K.flow.metric t).inner y a a * (K.flow.metric t).inner y b b -
        ((K.flow.metric t).inner y a b) ^ 2 ≠ 0 := by
      intro h
      have hs : g.inner y a a * g.inner y b b - (g.inner y a b) ^ 2 = 0 := by
        dsimp only [g]
        simp only [rescaledMetric_inner]
        calc
          _ = c ^ 2 * ((K.flow.metric t).inner y a a * (K.flow.metric t).inner y b b -
            ((K.flow.metric t).inner y a b) ^ 2) := by ring
          _ = 0 := by rw [h, mul_zero]
      rw [ha, hb, hab] at hs
      norm_num at hs
    rw [rescaledMetric_sectionalCurvature,
      (K.flow.connection t).sectionalCurvature_eq_of_orthonormal y c (hsec y) a b hgram,
      inv_mul_cancel₀ hc.ne']
  · refine ⟨0, sq_pos_of_pos hepsilon, fun y => ?_⟩
    rw [hmetric]
    simp [round_iterated_metric_derivative_zero, RiemannianMetric.tensorNorm]

theorem strongCanonicalNeighborhood_of_round
    (K : AncientKappaSolution 3 M) (hround : IsRoundAncientKappaSolution K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (C t : ℝ) (ht : t ≤ 0) (x : M) :
    M27StrongCanonicalNeighborhood K t x epsilon C := by
  obtain ⟨N⟩ := epsilonRoundComponent_of_roundSlice K ht hepsilon (hround t ht)
  exact .round N

end PoincareConjecture
