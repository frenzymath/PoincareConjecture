import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitDiameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Cap.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Strong
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.ProjectivePlaneLimit

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

theorem exists_noncompact_limit_without_neighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ kappa : ℝ, 0 < kappa → ∀ C₀ : ℝ, 0 < C₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
            ∀ S : NormalizedKappaSolutionSequence kappa,
              (∀ k, NoEmbeddedTrivialNormalProjectivePlane (S.term k).flow) →
              Tendsto (fun k => metricDiameter ((S.term k).flow.flow.metric 0) univ)
                atTop atTop →
              (∀ k, ¬ ∃ N : StrongEvolvingNeck (S.term k).flow 0 epsilon,
                N.center = (S.term k).base) →
              (∀ k, ¬ ∃ A : CapCertificate ((S.term k).flow.flow.metric 0),
                A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ (S.term k).base ∈ A.core) →
              ∃ G : M23InteriorConvergence S,
                M23TerminalExtension G ∧
                ¬ IsCompact (univ : Set G.limit.carrier.carrier) ∧
                NoEmbeddedTrivialNormalProjectivePlane G.limit.flow ∧
                (¬ ∃ N : StrongEvolvingNeck G.limit.flow 0 epsilon,
                  N.center = G.limit.base) ∧
                (¬ ∃ A : CapCertificate (G.limit.flow.flow.metric 0),
                  A.epsilon = epsilon ∧ A.cap_constant ≤ C₀ ∧ G.limit.base ∈ A.core) := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, htransport⟩ :=
    M23TerminalMetricConvergence.exists_cap_transport P
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro kappa hkappa C₀ hC₀
  obtain ⟨C, hC, hcaptransport⟩ := htransport kappa hkappa C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro epsilon _ hepsilon S hsource hdiam hnoneck hnocap
  obtain ⟨L⟩ := P.normalized_compactness ⟨kappa, hkappa, S⟩
  refine ⟨L.convergence, L.terminal_extension,
    L.not_isCompact_of_metricDiameter_tendsto hdiam,
    L.terminal_extension.noEmbeddedTrivialNormalProjectivePlane hsource, ?_, ?_⟩
  · rintro ⟨N, hcenter⟩
    have hepsilon' : epsilon < 1 / 200 :=
      (hepsilon.trans hsmall).trans_lt (by norm_num)
    obtain ⟨k, Nk, hbase, _, _⟩ :=
      (L.terminal_extension.eventually_strongEvolvingNeck_full_domain
        N hcenter hepsilon').exists
    exact hnoneck (L.convergence.subsequence k) ⟨Nk, hbase⟩
  · rintro ⟨A, hAepsilon, hAC₀, hbase⟩
    obtain ⟨e, he, hfixed, hconv⟩ := L.terminal_extension.terminal_embedding
    have hAthreshold : A.epsilon ≤ epsilon₀ := hAepsilon ▸ hepsilon
    obtain ⟨k, B, hBepsilon, hBC, _, hcore, _, _, _, _⟩ :=
      (hcaptransport hconv (fun k t ht x hx => hfixed k t 0 x ht le_rfl hx)
        A hAthreshold hAC₀).exists
    apply hnocap (L.convergence.subsequence k)
    refine ⟨B, hBepsilon.trans hAepsilon, hBC.le, ?_⟩
    rw [hcore]
    exact ⟨L.convergence.limit.base, hbase, congrArg Prod.snd (he k).2⟩

end PoincareConjecture
