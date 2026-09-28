import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.CollarSequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Cap.StrongCollar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Unlift











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe v u

namespace PoincareConjecture.CompactKappa

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace


def HasFineExteriorCap
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) (p : M) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧ delta < epsilon ∧
    ∃ A : CapCertificate (K.flow.metric 0),
      A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core ∧
      ∀ x : M, x ∉ A.core → ∃ N : StrongEvolvingNeck K 0 delta, N.center = x


theorem HasFineExteriorCap.of_ulift
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {K : AncientKappaSolution 3 M} {epsilon C : ℝ} {p : M}
    (h : HasFineExteriorCap (K.ulift : AncientKappaSolution 3 (ULift.{v} M))
      epsilon C (ULift.up p)) : HasFineExteriorCap K epsilon C p := by
  obtain ⟨delta, hd, hde, A, hA, hAC, hp, hneck⟩ := h
  refine ⟨delta, hd, hde, K.flow.capFromUlift 0 A, hA, hAC, hp, ?_⟩
  intro x hx
  obtain ⟨N, hN⟩ := hneck (ULift.up x) hx
  exact ⟨K.strongNeckFromUlift N, congrArg ULift.down hN⟩



theorem exists_noncompact_limit_without_strong_collars
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
              (∀ k, ¬ HasStrongCollarCap (S.term k).flow epsilon C (S.term k).base) →
              ∃ G : M23InteriorConvergence S,
                M23TerminalExtension G ∧
                ¬ IsCompact (univ : Set G.limit.carrier.carrier) ∧
                NoEmbeddedTrivialNormalProjectivePlane G.limit.flow ∧
                (¬ ∃ N : StrongEvolvingNeck G.limit.flow 0 epsilon,
                  N.center = G.limit.base) ∧
                ¬ HasFineExteriorCap G.limit.flow epsilon C₀ G.limit.base := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, htransport⟩ :=
    M23TerminalMetricConvergence.exists_cap_transport_with_strong_collar P
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
  · rintro ⟨delta, _, hdelta, A, hAepsilon, hAC₀, hbase, hcollar⟩
    obtain ⟨e, he, hfixed, hconv⟩ := L.terminal_extension.terminal_embedding
    have hAthreshold : A.epsilon ≤ epsilon₀ := hAepsilon ▸ hepsilon
    obtain ⟨k, B, hBepsilon, hBC, _, hcore, _, _, _, _, hBcollar⟩ :=
      (hcaptransport hconv (fun k t ht x hx => hfixed k t 0 x ht le_rfl hx)
        A hAthreshold hAC₀ delta (hAepsilon ▸ hdelta)
        (fun x hx => hcollar x hx.2)).exists
    apply hnocap (L.convergence.subsequence k)
    refine ⟨B, hBepsilon.trans hAepsilon, hBC.le, ?_, ?_⟩
    · rw [hcore]
      exact ⟨L.convergence.limit.base, hbase, congrArg Prod.snd (he k).2⟩
    · intro x hx hxc
      exact hAepsilon ▸ hBcollar x ⟨hx, hxc⟩

end PoincareConjecture.CompactKappa
