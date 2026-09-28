import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Stability
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitEmbedding

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance coreCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

theorem M23TerminalExtension.not_isCompact_of_noncompact_sources
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    (hnoncompact : ∀ k, ¬ IsCompact (univ : Set (S.term k).carrier.carrier)) :
    ¬ IsCompact (univ : Set G.limit.carrier.carrier) := by
  intro hcompact
  obtain ⟨k, hk⟩ := (G.eventually_exhaustion_eq_univ hcompact).exists
  obtain ⟨e, _, _, _⟩ := hterminal.terminal_embedding
  let f := fun x => ((e k).toFun (0, x)).2
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x =>
    ((e k).spatial_contMDiffAt (G.exhaustion_open k)
      (mem_Iic.mpr le_rfl) (hk ▸ mem_univ x)).continuousAt
  have hsurj : Function.Surjective f :=
    (e k).spatial_surjective_of_compact hk hcompact (mem_Iic.mpr le_rfl)
  have hsource := hcompact.image hf
  rw [image_univ, range_eq_univ.mpr hsurj] at hsource
  exact hnoncompact (G.subsequence k) hsource

theorem M23TerminalExtension.not_strongEvolvingNeck_at_soul_limit
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    (hnoncompact : ∀ k, NoncompactSpace (S.term k).carrier.carrier)
    (hsoul : ∀ k, ∃ P : RiemannianMetric.PointSoulData ((S.term k).flow.flow.metric 0),
      P.center = (S.term k).base)
    {δ : ℝ} (hδ : δ < min neckSeparationThreshold (1 / 4)) :
    ¬ ∃ N : StrongEvolvingNeck G.limit.flow 0 δ, N.center = G.limit.base := by
  rintro ⟨N, hcenter⟩
  let ε := (δ + min neckSeparationThreshold (1 / 4)) / 2
  have hδε : δ < ε := by dsimp [ε]; linarith
  have hεmin : ε < min neckSeparationThreshold (1 / 4) := by dsimp [ε]; linarith
  have hεsmall : ε ≤ neckSeparationThreshold :=
    (hεmin.trans_le (min_le_left _ _)).le
  have hε : ε < 1 / 4 := hεmin.trans_le (min_le_right _ _)
  obtain ⟨k, Nk, hbase, _, _⟩ :=
    (hterminal.eventually_strongEvolvingNeck N hcenter hδε hε).exists
  letI := hnoncompact (G.subsequence k)
  obtain ⟨P, hP⟩ := hsoul (G.subsequence k)
  exact P.not_strongEvolvingNeck_center (S.term (G.subsequence k)).flow hεsmall
    ⟨Nk, hbase.trans hP.symm⟩

end PoincareConjecture
