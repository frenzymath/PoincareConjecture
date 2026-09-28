import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.SectionalConvergenceBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Lower.TrichotomyTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace

theorem normalized_compact_uniform_sectional_lower
    (P : M27KappaAlternativePredecessors.{u})
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : BasedKappaSolution kappa,
      IsCompact (univ : Set K.carrier.carrier) →
      metricDiameter (K.flow.flow.metric 0) univ ≤ D →
      ∀ x : K.carrier.carrier, ∀ v w : TangentSpace (𝓡 3) x,
        LinearIndependent ℝ ![v, w] →
        c < (K.flow.flow.connection 0).sectionalCurvature x v w := by
  classical
  by_contra h
  push Not at h
  have hbad (k : ℕ) := h (1 / ((k : ℝ) + 1)) (by positivity)
  choose K hcompact hdiam x v w hind hfail using hbad
  let S : NormalizedKappaSolutionSequence kappa := ⟨hkappa, K⟩
  obtain ⟨L⟩ := P.normalized_compactness ⟨kappa, hkappa, S⟩
  have hlimit := L.terminal_extension.isCompact_of_uniform_source_diameter hD hcompact hdiam
  let : CompactSpace L.convergence.limit.carrier.carrier := ⟨hlimit⟩
  have hpositive : (L.convergence.limit.flow.flow.connection 0).StrictlyPositiveSectionalCurvature :=
    positiveSectionalCurvature_of_ulift
      ((L.convergence.limit.flow.ulift : AncientKappaSolution 3
        (ULift.{u} L.convergence.limit.carrier.carrier)).positiveSectionalCurvature_of_compact
          P.classificationServices isCompact_univ 0 le_rfl)
  obtain ⟨c, hc, heventual⟩ :=
    L.terminal_extension.exists_pos_eventually_source_ball_sectional_lower_bound
      hpositive (show 0 < D + 1 by linarith)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  obtain ⟨k, hk, hkbound⟩ := (heventual.and
    (L.convergence.subsequence_strictMono.tendsto_atTop.eventually
      (eventually_ge_atTop n))).exists
  have hnk : (n : ℝ) ≤ L.convergence.subsequence k := by exact_mod_cast hkbound
  have hsmall : 1 / ((L.convergence.subsequence k : ℝ) + 1) < c :=
    (one_div_le_one_div_of_le (by positivity) (by linarith)).trans_lt hn
  have hball : x (L.convergence.subsequence k) ∈
      ((S.term (L.convergence.subsequence k)).flow.flow.metric 0).ball
        (S.term (L.convergence.subsequence k)).base (D + 1) :=
    compact_mem_ball_of_metricDiameter_lt _ (hcompact _)
      ((hdiam _).trans_lt (by linarith)) _ _
  have hlarge := hk (x (L.convergence.subsequence k)) hball
    (v (L.convergence.subsequence k)) (w (L.convergence.subsequence k))
    (hind (L.convergence.subsequence k))
  exact (not_lt_of_ge (hfail (L.convergence.subsequence k))) (hsmall.trans hlarge)

end PoincareConjecture
