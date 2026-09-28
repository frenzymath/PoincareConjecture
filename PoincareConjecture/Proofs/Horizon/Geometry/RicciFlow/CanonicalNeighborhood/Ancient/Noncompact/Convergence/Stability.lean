import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.UniformJets
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalStabilityCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected



theorem M23TerminalExtension.eventually_strongEvolvingNeck
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    {δ ε : ℝ} (N : StrongEvolvingNeck G.limit.flow 0 δ)
    (hcenter : N.center = G.limit.base) (hδε : δ < ε) (hε : ε < 1 / 4) :
    ∀ᶠ k in Filter.atTop,
      ∃ Nk : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 ε,
        Nk.center = (S.term (G.subsequence k)).base ∧
        Nk.duration = 1 ∧ Nk.terminal_neck.scale = 1 := by
  obtain ⟨e, he, hfixed, hconv⟩ := hterminal.terminal_embedding
  have hδ : 0 < δ := by rw [← N.terminal_epsilon]; exact N.terminal_neck.epsilon_pos
  have hεpos : 0 < ε := hδ.trans hδε
  have hsmall : N.terminal_neck.epsilon < ε := by rw [N.terminal_epsilon]; exact hδε
  have hnormalize : (G.limit.flow.flow.connection 0).scalarCurvature N.center = 1 := by
    rw [hcenter]
    exact G.limit.scalar_normalized
  have hclose : RoundCylinderFamilyClose N.terminal_neck.epsilon (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback (G.limit.flow.flow.metric u) N.terminal_neck.coordinate_map) := by
    rw [N.terminal_epsilon]
    simpa only [hnormalize, div_one, zero_add, one_mul] using N.metric_comparison
  have hc := hconv.eventually_terminalCylinder_familyClose hfixed
    N.terminal_neck.epsilon_pos hsmall N.terminal_neck.coordinate_map_smooth hclose
  have hcentral := N.terminal_neck.center_on_central_sphere
  rw [N.terminal_neck.central_sphere_eq] at hcentral
  obtain ⟨z, hz, hzmap⟩ := hcentral
  have hq : N.terminal_neck.coordinate_map (z.1, 0) = G.limit.base := by
    have hz0 : z.2 = 0 := mem_singleton_iff.mp hz.2
    have hz' : z = (z.1, 0) := Prod.ext rfl hz0
    rw [← hz']
    simpa only [N.terminal_center, hcenter] using hzmap
  filter_upwards [hc, G.eventually_terminalNeckEmbedding e N.terminal_neck hsmall]
    with k hclosek hemb
  let f := G.terminalNeckEmbedding e N.terminal_neck ε k
  obtain ⟨hsource, hsmooth, hinverse, hcentral⟩ := hemb
  have hnormsource := (S.term (G.subsequence k)).scalar_normalized
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hclosezero : RoundCylinderClose ε 0
      (roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0) f) := by
    obtain ⟨hs, B, hB, hb⟩ := hclosek
    exact ⟨hs 0 hzero, B, hB, hb 0 hzero⟩
  let neck : EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0) := {
    epsilon := ε
    epsilon_pos := hεpos
    epsilon_lt_half := by linarith
    scale := 1
    scale_pos := zero_lt_one
    center := (S.term (G.subsequence k)).base
    connection := (S.term (G.subsequence k)).flow.flow.connection 0
    scalar_center_pos := by rw [hnormsource]; exact zero_lt_one
    scale_eq_scalar := by rw [hnormsource, Real.one_rpow]
    carrier := f.target
    carrier_open := f.open_target
    coordinate := neckDomainCoordinates f hsource
    coordinate_map := f
    coordinate_map_eq := fun z => rfl
    coordinate_map_smooth := hsmooth
    coordinate_inverse := f.symm
    coordinate_inverse_mem := fun x hx => neckDomainCoordinates_inverse_mem f hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left f hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right f hsource
    coordinate_inverse_smooth := hinverse
    central_sphere := f '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := ⟨(z.1, 0), ⟨mem_univ _, mem_singleton _⟩,
      G.terminalNeckEmbedding_center e (fun k => (he k).2) N.terminal_neck ε k z.1 hq⟩
    central_sphere_subset := hcentral
    metric_comparison := ⟨by simpa only [inv_one, one_pow, one_mul] using hclosezero⟩
  }
  refine ⟨{
    time_mem := le_rfl
    center := (S.term (G.subsequence k)).base
    duration := 1
    duration_pos := zero_lt_one
    normalized_duration := by simpa only [one_mul] using hnormsource
    terminal_neck := neck
    terminal_center := rfl
    terminal_epsilon := rfl
    terminal_connection := rfl
    metric_comparison := ?_
  }, rfl, rfl, rfl⟩
  have hmap : neck.coordinate_map =
      (fun z => ((e k).toFun (0, N.terminal_neck.coordinate_map z)).2) := rfl
  simpa only [hnormsource, div_one, zero_add, one_mul, hmap] using hclosek

end PoincareConjecture
