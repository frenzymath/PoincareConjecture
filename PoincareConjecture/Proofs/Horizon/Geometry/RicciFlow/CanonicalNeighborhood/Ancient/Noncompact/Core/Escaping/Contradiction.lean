import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Cylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Stability

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

theorem M23TerminalExtension.eventually_strongEvolvingNeck_of_line_of_services
    (P : NoncompactKappaServices.{u})
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hplane : ∀ k, NoEmbeddedTrivialNormalProjectivePlane (S.term k).flow)
    (γ : ℝ → G.limit.carrier.carrier)
    (hγ : ∀ s t : ℝ, (G.limit.flow.flow.metric 0).edist (γ s) (γ t) =
      ENNReal.ofReal |s - t|)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) :
    ∀ᶠ k in atTop,
      ∃ N : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 epsilon,
        N.center = (S.term (G.subsequence k)).base := by
  obtain ⟨C, A, _, ⟨H⟩, e, hmetric⟩ := T.exists_round_factor_of_line_of_services P γ hγ
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  obtain ⟨N, hcenter⟩ := exists_strongEvolvingNeck_of_round_factor G.limit.flow A H
    (T.noEmbeddedTrivialNormalProjectivePlane hplane) e hmetric
    (show 0 < epsilon / 2 by linarith) (show epsilon / 2 < 1 / 2 by linarith)
    G.limit.base
  exact (T.eventually_strongEvolvingNeck N hcenter (by linarith) hεsmall).mono
    (fun _ ⟨Nk, hc, _, _⟩ => ⟨Nk, hc⟩)

theorem M23TerminalExtension.eventually_strongEvolvingNeck_of_line
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hplane : ∀ k, NoEmbeddedTrivialNormalProjectivePlane (S.term k).flow)
    (γ : ℝ → G.limit.carrier.carrier)
    (hγ : ∀ s t : ℝ, (G.limit.flow.flow.metric 0).edist (γ s) (γ t) =
      ENNReal.ofReal |s - t|)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) :
    ∀ᶠ k in atTop,
      ∃ N : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 epsilon,
        N.center = (S.term (G.subsequence k)).base := by
  exact M23TerminalExtension.eventually_strongEvolvingNeck_of_line_of_services P.noncompactServices T hplane γ hγ hε hεsmall

theorem M23TerminalExtension.eventually_strongEvolvingNeck_of_nearby_necks_of_services
    (P : NoncompactKappaServices.{u})
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hnoncompact : ∀ k, NoncompactSpace (S.term k).carrier.carrier)
    (soul : ∀ k, RiemannianMetric.PointSoulData ((S.term k).flow.flow.metric 0))
    (neck : ∀ k, EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0))
    (hsmall : ∀ k, (neck k).epsilon ≤ neckSeparationThreshold)
    {Bcenter : ℝ} (hBcenter : 0 ≤ Bcenter)
    (hnear : ∀ k, (((S.term (G.subsequence k)).flow.flow.metric 0).edist
      (neck k).center (S.term (G.subsequence k)).base).toReal ≤ Bcenter)
    {B : ℝ} (hB : 0 ≤ B) (hscale : ∀ k, (neck k).scale ≤ B)
    (hescape : Tendsto (fun k =>
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist
        (soul (G.subsequence k)).center (S.term (G.subsequence k)).base).toReal)
      atTop atTop)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) :
    ∀ᶠ k in atTop,
      ∃ N : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 epsilon,
        N.center = (S.term (G.subsequence k)).base := by
  obtain ⟨γ, hγ⟩ := T.exists_minimizing_line_of_nearby_necks
    (fun k => hnoncompact (G.subsequence k)) (fun k => soul (G.subsequence k))
    neck hsmall hBcenter hnear hB hscale hescape
  exact T.eventually_strongEvolvingNeck_of_line_of_services P
    (fun k => (soul k).noEmbeddedTrivialNormalProjectivePlane (S.term k).flow)
    γ hγ hε hεsmall

theorem M23TerminalExtension.eventually_strongEvolvingNeck_of_nearby_necks
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hnoncompact : ∀ k, NoncompactSpace (S.term k).carrier.carrier)
    (soul : ∀ k, RiemannianMetric.PointSoulData ((S.term k).flow.flow.metric 0))
    (neck : ∀ k, EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0))
    (hsmall : ∀ k, (neck k).epsilon ≤ neckSeparationThreshold)
    {Bcenter : ℝ} (hBcenter : 0 ≤ Bcenter)
    (hnear : ∀ k, (((S.term (G.subsequence k)).flow.flow.metric 0).edist
      (neck k).center (S.term (G.subsequence k)).base).toReal ≤ Bcenter)
    {B : ℝ} (hB : 0 ≤ B) (hscale : ∀ k, (neck k).scale ≤ B)
    (hescape : Tendsto (fun k =>
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist
        (soul (G.subsequence k)).center (S.term (G.subsequence k)).base).toReal)
      atTop atTop)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) :
    ∀ᶠ k in atTop,
      ∃ N : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 epsilon,
        N.center = (S.term (G.subsequence k)).base := by
  exact M23TerminalExtension.eventually_strongEvolvingNeck_of_nearby_necks_of_services P.noncompactServices T hnoncompact soul neck hsmall hBcenter hnear hB hscale hescape hε hεsmall

end PoincareConjecture
