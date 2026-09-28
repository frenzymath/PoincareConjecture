import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Contradiction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

theorem uniform_strongNeck_of_nearby_neck_and_distant_soul_of_services
    (P : NoncompactKappaServices.{u})
    {kappa epsilon B Bcenter : ℝ} (hkappa : 0 < kappa) (hε : 0 < epsilon)
    (hεsmall : epsilon < 1 / 4) (hB : 0 ≤ B) (hBcenter : 0 ≤ Bcenter) :
    ∃ L : ℝ, 0 < L ∧ ∀ K : BasedKappaSolution kappa,
      NoncompactSpace K.carrier.carrier →
      ∀ soul : RiemannianMetric.PointSoulData (K.flow.flow.metric 0),
      ∀ neck : EpsilonNeck (K.flow.flow.metric 0),
        neck.epsilon ≤ neckSeparationThreshold →
        ((K.flow.flow.metric 0).edist neck.center K.base).toReal ≤ Bcenter →
        neck.scale ≤ B →
        L < ((K.flow.flow.metric 0).edist soul.center K.base).toReal →
        ∃ N : StrongEvolvingNeck K.flow 0 epsilon, N.center = K.base := by
  classical
  by_contra h
  push_neg at h
  have hbad (k : ℕ) := h ((k : ℝ) + 1) (by positivity)
  choose K hnoncompact soul neck hsmall hnear hscale hd hfail using hbad
  let S : NormalizedKappaSolutionSequence kappa := ⟨hkappa, K⟩
  obtain ⟨L⟩ := P.normalized_compactness ⟨kappa, hkappa, S⟩
  have hescape : Tendsto (fun k =>
      (((S.term k).flow.flow.metric 0).edist (soul k).center (S.term k).base).toReal)
      atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    obtain ⟨n, hn⟩ := exists_nat_gt a
    filter_upwards [eventually_ge_atTop n] with k hk
    have hnk : (n : ℝ) ≤ k := by exact_mod_cast hk
    exact le_of_lt (lt_trans hn (lt_trans (by linarith) (hd k)))
  have hneck := L.terminal_extension.eventually_strongEvolvingNeck_of_nearby_necks_of_services P
    hnoncompact soul (fun k => neck (L.convergence.subsequence k))
    (fun k => hsmall (L.convergence.subsequence k)) hBcenter
    (fun k => hnear (L.convergence.subsequence k)) hB
    (fun k => hscale (L.convergence.subsequence k))
    (hescape.comp L.convergence.subsequence_strictMono.tendsto_atTop) hε hεsmall
  obtain ⟨k, N, hN⟩ := hneck.exists
  exact hfail (L.convergence.subsequence k) N hN

theorem uniform_strongNeck_of_nearby_neck_and_distant_soul
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa epsilon B Bcenter : ℝ} (hkappa : 0 < kappa) (hε : 0 < epsilon)
    (hεsmall : epsilon < 1 / 4) (hB : 0 ≤ B) (hBcenter : 0 ≤ Bcenter) :
    ∃ L : ℝ, 0 < L ∧ ∀ K : BasedKappaSolution kappa,
      NoncompactSpace K.carrier.carrier →
      ∀ soul : RiemannianMetric.PointSoulData (K.flow.flow.metric 0),
      ∀ neck : EpsilonNeck (K.flow.flow.metric 0),
        neck.epsilon ≤ neckSeparationThreshold →
        ((K.flow.flow.metric 0).edist neck.center K.base).toReal ≤ Bcenter →
        neck.scale ≤ B →
        L < ((K.flow.flow.metric 0).edist soul.center K.base).toReal →
        ∃ N : StrongEvolvingNeck K.flow 0 epsilon, N.center = K.base := by
  exact uniform_strongNeck_of_nearby_neck_and_distant_soul_of_services P.noncompactServices hkappa hε hεsmall hB hBcenter

end PoincareConjecture
