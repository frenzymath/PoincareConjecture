import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Lower.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.SectionalConvergenceBounds

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

theorem normalized_uniform_soul_core_sectional_lower_of_services
    (P : NoncompactKappaServices.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : BasedKappaSolution kappa,
      NoncompactSpace K.carrier.carrier →
      (∃ soul : RiemannianMetric.PointSoulData (K.flow.flow.metric 0),
        soul.center = K.base) →
      ∀ x ∈ (K.flow.flow.metric 0).ball K.base D,
      ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
        c < (K.flow.flow.connection 0).sectionalCurvature x v w := by
  classical
  by_contra h
  push Not at h
  have hbad (k : ℕ) := h (1 / ((k : ℝ) + 1)) (by positivity)
  choose K hnoncompact hsoul x hx v w hind hfail using hbad
  let S : NormalizedKappaSolutionSequence kappa := ⟨hkappa, K⟩
  obtain ⟨L⟩ := P.normalized_compactness ⟨kappa, hkappa, S⟩
  have hpositive := L.terminal_extension.positiveSectionalCurvature_of_pointSouls
    htrichotomy hnoncompact hsoul
  obtain ⟨c, hc, heventual⟩ :=
    L.terminal_extension.exists_pos_eventually_source_ball_sectional_lower_bound hpositive hD
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  obtain ⟨k, hk, hkbound⟩ := (heventual.and
    (L.convergence.subsequence_strictMono.tendsto_atTop.eventually
      (eventually_ge_atTop n))).exists
  have hnk : (n : ℝ) ≤ L.convergence.subsequence k := by exact_mod_cast hkbound
  have hsmall : 1 / ((L.convergence.subsequence k : ℝ) + 1) < c :=
    (one_div_le_one_div_of_le (by positivity) (by linarith)).trans_lt hn
  have hlarge := hk (x (L.convergence.subsequence k)) (hx (L.convergence.subsequence k))
    (v (L.convergence.subsequence k)) (w (L.convergence.subsequence k))
    (hind (L.convergence.subsequence k))
  exact (not_lt_of_ge (hfail (L.convergence.subsequence k))) (hsmall.trans hlarge)

theorem normalized_uniform_soul_core_sectional_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : BasedKappaSolution kappa,
      NoncompactSpace K.carrier.carrier →
      (∃ soul : RiemannianMetric.PointSoulData (K.flow.flow.metric 0),
        soul.center = K.base) →
      ∀ x ∈ (K.flow.flow.metric 0).ball K.base D,
      ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
        c < (K.flow.flow.connection 0).sectionalCurvature x v w := by
  exact normalized_uniform_soul_core_sectional_lower_of_services P.noncompactServices htrichotomy hkappa hD

end PoincareConjecture
