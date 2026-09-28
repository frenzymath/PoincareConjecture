import PoincareConjecture.Proofs.M35.Thm12_28.LimitAlternatives
import PoincareConjecture.Proofs.M35.CapGeometry.CertificateConnection
import PoincareConjecture.Proofs.M09.TensorEvaluationBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem equal_metric_neck
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (heq : g = h) (D : LeviCivitaData h) :
    ∃ N' : EpsilonNeck h, N'.epsilon = N.epsilon ∧
      N'.connection = D ∧ N'.carrier = N.carrier := by
  subst h
  exact ⟨N.withConnection D, rfl, rfl, rfl⟩

theorem exists_limit_fine_neck (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
        (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
        (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
        (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
        (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
          (blowupBackwardInterval ⊤)) {kappa : ℝ}
        (_A : BlowupAncientKappaIdentification L.limit kappa),
        letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
        letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
        letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
          L.limit.carrier.chartedSpace
        letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
        letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
        letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
        letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
        letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
        ∃ N : EpsilonNeck (L.limit.flow.metric 0), N.epsilon = epsilon ∧
          N.connection = L.limit.flow.connection 0 ∧ IsCompact (closure N.carrier) ∧
          ∃ j : ℕ, closure N.carrier ⊆ L.exhaustion.space j := by
  obtain ⟨delta, hdelta, hmodels⟩ := exists_limit_cap_or_neck_constants P
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon he hsmall g₀ E t x ht hR L kappa A
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  obtain ⟨C, _hC, hcanonical⟩ := hmodels epsilon he hsmall
  obtain ⟨N, hNe, hNc, j, hNj⟩ :
      ∃ N : EpsilonNeck (A.solution.flow.metric 0), N.epsilon = epsilon ∧
        IsCompact (closure N.carrier) ∧ ∃ j : ℕ,
          closure N.carrier ⊆ L.exhaustion.space j := by
    rcases hcanonical g₀ E t x ht hR L kappa A 0 le_rfl L.limit.base with
      ⟨N, _hcenter, j, hstage⟩ | ⟨N, j, hstage⟩
    · exact ⟨N.terminal_neck, N.terminal_epsilon,
        N.terminal_neck.isCompact_closure (A.solution.complete 0 le_rfl), j, hstage⟩
    · exact ⟨N.cap.end_neck, N.cap.end_neck_epsilon.trans N.epsilon_eq,
        N.cap.end_neck.isCompact_closure (A.solution.complete 0 le_rfl), j,
        (closure_mono N.cap.end_neck_subset).trans hstage⟩
  obtain ⟨N', he', hD, hU⟩ := equal_metric_neck N (A.metric_eq 0 le_rfl)
    (L.limit.flow.connection 0)
  refine ⟨N', he'.trans hNe, hD, ?_, j, ?_⟩
  · rwa [hU]
  · rwa [hU]

private theorem scalar_of_equal_metrics
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (heq : g = h)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (y : M) :
    D.scalarCurvature y = D'.scalarCurvature y := by
  subst h
  exact D.scalarCurvature_eq D' y

theorem blowupSequence_limit_scalar_ceiling (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∃ B : ℝ, 0 < B ∧ ∀ y : L.limit.carrier.carrier,
      (L.limit.flow.connection 0).scalarCurvature y ≤ B := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  obtain ⟨K, hK, hbound⟩ := A.solution.bounded_curvature 0 le_rfl
  refine ⟨9 * K + 1, by positivity, ?_⟩
  intro y
  rw [← scalar_of_equal_metrics (A.metric_eq 0 le_rfl)
    (A.solution.flow.connection 0) (L.limit.flow.connection 0) y]
  have hs := Proofs.M09.scalar_abs_le_curvatureTensorNorm P.curvature
    (A.solution.flow.metric 0) (A.solution.flow.connection 0) y
  have hn := (le_abs_self _).trans (hbound y)
  have ha := le_abs_self ((A.solution.flow.connection 0).scalarCurvature y)
  norm_num only [Nat.cast_ofNat, OfNat.ofNat, sq] at hs
  linarith only [hs, hn, ha]

end PoincareConjecture.M35.OrdinaryRealization
