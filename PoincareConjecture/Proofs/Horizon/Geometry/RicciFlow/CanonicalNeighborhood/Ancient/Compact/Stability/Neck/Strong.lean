import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Static
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainEvolving
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.EscapeCarrier











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23InteriorConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  (G : M23InteriorConvergence S)
  (e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j))



theorem exists_terminalStrongNeck_of_fullFamily
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (hcenter : N.center = G.limit.base)
    (k : ℕ)
    (hbase : (e k).toFun (0, G.limit.base) = (0, (S.term (G.subsequence k)).base))
    (hsource : (G.terminalNeckEmbedding e N N.epsilon k).source = N.cylinderDomain)
    (hclose : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric u)
        (G.terminalNeckEmbedding e N N.epsilon k))) :
    ∃ Nk : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 N.epsilon,
      Nk.center = (S.term (G.subsequence k)).base ∧
      Nk.duration = 1 ∧ Nk.terminal_neck.scale = 1 ∧
      Nk.terminal_neck.coordinate_map = G.terminalNeckEmbedding e N N.epsilon k ∧
      Nk.terminal_neck.carrier = (G.terminalNeckEmbedding e N N.epsilon k).target := by
  have hnormsource := (S.term (G.subsequence k)).scalar_normalized
  have hb : ((e k).toFun (0, N.center)).2 = (S.term (G.subsequence k)).base := by
    rw [hcenter, hbase]
  have hnormimage : ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
      ((e k).toFun (0, N.center)).2 = 1 := by
    rw [hb, hnormsource]
  have hR : 0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
      ((e k).toFun (0, N.center)).2 := by rw [hnormimage]; exact zero_lt_one
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hclosezero : RoundCylinderClose N.epsilon 0 (fun z v w =>
      ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
          ((e k).toFun (0, N.center)).2 *
        roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
          (G.terminalNeckEmbedding e N N.epsilon k) z v w) := by
    obtain ⟨hs, B, hB, hbound⟩ := hclose
    simpa only [hnormimage, one_mul] using
      (show RoundCylinderClose N.epsilon 0
        (roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
          (G.terminalNeckEmbedding e N N.epsilon k)) from
        ⟨hs 0 hzero, B, hB, hbound 0 hzero⟩)
  let neck := G.terminalStaticNeck e N N.epsilon_pos N.epsilon_lt_half k hsource hR hclosezero
  have hmap : neck.coordinate_map = G.terminalNeckEmbedding e N N.epsilon k := rfl
  let Nk : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 N.epsilon := {
    time_mem := le_rfl
    center := (S.term (G.subsequence k)).base
    duration := 1
    duration_pos := zero_lt_one
    normalized_duration := by simpa only [one_mul] using hnormsource
    terminal_neck := neck
    terminal_center := hb
    terminal_epsilon := rfl
    terminal_connection := rfl
    metric_comparison := by
      simpa only [hnormsource, div_one, zero_add, one_mul, hmap] using hclose }
  refine ⟨Nk, rfl, rfl, ?_, rfl, rfl⟩
  change (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
    ((e k).toFun (0, N.center)).2) ^ (-1 / 2 : ℝ) = 1
  rw [hnormimage, Real.one_rpow]

end M23InteriorConvergence



theorem M23TerminalExtension.eventually_strongEvolvingNeck_full_domain
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    {epsilon : ℝ} (N : StrongEvolvingNeck G.limit.flow 0 epsilon)
    (hcenter : N.center = G.limit.base) (hsmall : epsilon < 1 / 200) :
    ∀ᶠ k in atTop,
      ∃ Nk : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 epsilon,
        Nk.center = (S.term (G.subsequence k)).base ∧
        Nk.duration = 1 ∧ Nk.terminal_neck.scale = 1 := by
  obtain ⟨e, he, hfixed, hconv⟩ := hterminal.terminal_embedding
  have hnormalize : (G.limit.flow.flow.connection 0).scalarCurvature N.center = 1 := by
    rw [hcenter]
    exact G.limit.scalar_normalized
  have hclose : RoundCylinderFamilyClose N.terminal_neck.epsilon (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback (G.limit.flow.flow.metric u)
        N.terminal_neck.coordinate_map) := by
    rw [N.terminal_epsilon]
    simpa only [hnormalize, div_one, zero_add, one_mul] using N.metric_comparison
  have hcompact := N.terminal_neck.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl)
  have hsmall' : N.terminal_neck.epsilon < 1 / 200 := by
    rw [N.terminal_epsilon]
    exact hsmall
  filter_upwards [hconv.eventually_terminalNeck_full_familyClose hfixed
      N.terminal_neck hcompact hsmall' hclose,
    G.eventually_terminalNeckEmbedding_full e N.terminal_neck hcompact]
    with k hfamily hcoordinates
  obtain ⟨Nk, hc, hd, hs, _, _⟩ := G.exists_terminalStrongNeck_of_fullFamily e
    N.terminal_neck (N.terminal_center.trans hcenter) k (he k).2 hcoordinates.1 hfamily
  have hresult : ∃ Nk : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0
      N.terminal_neck.epsilon,
      Nk.center = (S.term (G.subsequence k)).base ∧
      Nk.duration = 1 ∧ Nk.terminal_neck.scale = 1 := ⟨Nk, hc, hd, hs⟩
  rw [← N.terminal_epsilon]
  exact hresult

end PoincareConjecture
