import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Predecessors
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Operation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Compactness.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Pinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.ProjectivePlane
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Pinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Topology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.FiniteEnd

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

open Surgery.Terminal.Gluing SurgeryEventRebuild Surgery

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B in
set_option maxHeartbeats 1200000 in
theorem continuation_of_finite_cuts (P : M33Predecessors.{u})
    (σ : Ico H.reference.tMinus T) (hclose : T - (F.parameters.h T) ^ 2 < σ.1)
    {ι : Type u} [Fintype ι]
    (J : ι → MetricSurgeryInput F.local_constants (N.limit.extension.extended.metric T))
    (R : ∀ i, MetricSurgeryResult F.standard_initial (J i))
    (U : Opens (N.limit.extension.extended.slice T).carrier) (hU : Nonempty U)
    (hd : Pairwise (fun i j => Disjoint
      ((J i).negativeHalf : Set (N.limit.extension.extended.slice T).carrier) (J j).negativeHalf))
    (hc : ∀ i, Disjoint (U : Set (N.limit.extension.extended.slice T).carrier)
      (J i).neck.central_sphere)
    (hneck : Pairwise (fun i j => Disjoint (J i).neck.carrier (J j).neck.carrier))
    (hUn : ∀ i, (U : Set (N.limit.extension.extended.slice T).carrier) ∩
      (J i).neck.carrier = (J i).negativeHalf)
    (hfront : frontier (U : Set (N.limit.extension.extended.slice T).carrier) ⊆
      ⋃ i, (J i).neck.central_sphere)
    (hcompact : IsCompact (closure (U : Set (N.limit.extension.extended.slice T).carrier)))
    (hcore : {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} ⊆ U)
    (htime : ∀ i, (J i).time = T)
    (hdelta : ∀ i, (J i).neck.epsilon = F.parameters.delta T)
    (hscale : ∀ i, (J i).neck.scale = F.parameters.h T)
    (cuts : ∀ i, SurgeryEndCut (J i).neck)
    (hretained : closure (U : Set (N.limit.extension.extended.slice T).carrier) =
      SurgeryTerminalCoreComponents (N.limit.extension.extended.connection T) I.rho \
        ⋃ i, (cuts i).tail)
    (hcoreNe : I.controlled_core.Nonempty)
    (ν : ι → TerminalStrongNeck N.limit.extension (F.parameters.delta T))
    (hJneck : ∀ i, (J i).neck = (ν i).spatialNeck
      ((hdelta i) ▸ (J i).neck.epsilon_lt_half)) :
    Nonempty (RepairedBranchContinuationData I) := by
  let C := cutCarrier J R U hU hd hc
  let g := cutMetric J R U hU hd hc
  let : Nonempty C.carrier := cutCarrier_nonempty J R U hU hd hc
  let : CompactSpace C.carrier := cutCarrier_compact J R U hU hd hc hcompact hfront
    (fun i => (hUn i).symm.subset.trans inter_subset_left)
    (fun i x hx => (hUn i).subset ⟨hx.1, (J i).neck.region_subset_carrier (-1) 1 hx.2⟩)
  have hC : IsCompact (univ : Set C.carrier) := isCompact_univ
  have hRP : SurgeryNoTwoSidedProjectivePlane C :=
    cutCarrier_noTwoSidedProjectivePlane J R U hU hd hc hneck hUn
      (B.terminal_no_two_sided_projective_plane N.limit)
  have hp : HamiltonIveyPinchedAt g.leviCivitaData T :=
    (TerminalRestart.pinchedAt_iff_hamiltonIvey g.leviCivitaData T).mp
      (cutMetric_pinched J R U hU hd hc (N.limit.extension.extended.connection T) T
        (Terminal.terminal_pinched H N.limit) htime)
  obtain ⟨b, hb, O, hO, hpinch, _hmax, hblow⟩ :=
    P.exists_pinched_restart g g.leviCivitaData T I.terminal_pos.le hp
  have hPost : (⟨C, g⟩ : SliceMetric.{u}) = Splice.family F T C O T := by
    rw [Splice.family_after F T C O le_rfl, hO]
  let E := B.assembleNonemptyEvent σ hclose J R U hU hd hc hneck hUn hfront
    hcompact hcore htime hdelta hscale (Splice.family F T C O)
    (fun t ht => (Splice.family_before F T C O ht).symm) hPost
  let W := TerminalRestart.canonicalNonemptyEvent I C O E
  let compat := B.assembleNonemptyEvent_slab_compatibility σ hclose J R U hU hd hc
    hneck hUn hfront hcompact hcore htime hdelta hscale O hPost
  let A := TerminalRestart.extension I C O W hC hRP hb hblow compat
  have hT : T ∈ A.extended.surgery_times := mem_insert _ _
  let hpost : Nonempty (A.extended.slice T).carrier :=
    TerminalRestart.slices_nonempty I C O T I.terminal_pos.le
  have hboundaries : ∀ i, Nonempty (SurgeryTerminalStrongNeck A.extended T hT i) :=
    B.assembled_terminal_strong_boundaries σ hclose J R U hU hd hc hneck hUn hfront
      hcompact hcore htime hdelta hscale O hPost hC hRP hb hblow ν hJneck hT
  refine ⟨⟨{
    extension := A
    old_event_data := TerminalRestart.old_event_preservation I C O W hC hRP hb hblow compat
    end_time := b
    extends_past := hb
    time_domain_eq := rfl
    surgery_at_terminal := hT
    terminal_operation := .nonempty hpost
      (B.assembledNonemptyOperation σ hclose J R U hU hd hc hneck hUn hfront hcompact hcore
        htime hdelta hscale O hPost hC hRP hb hblow cuts hretained hcoreNe hT)
    terminal_nonempty_iff := ⟨fun _ => hpost, fun _ => hcoreNe⟩
    terminal_empty_iff := ?_
    terminal_empty_end_time_top := fun h => (hcoreNe.ne_empty h).elim
    post_terminal_interval := TerminalRestart.post_terminal_interval I C O W hC hRP hb hblow compat
    admissible := TerminalRestart.admissible_from_terminal_boundaries I C O E hC hRP hb hblow
      compat hboundaries
    pinched := TerminalRestart.pinched_of_hamiltonIvey I C O W hC hRP hb hblow compat hpinch
    extinction_permanent := A.extended.extinction_permanent
    no_later_surgery := fun t _ ht => TerminalRestart.no_later_surgery I C O W hC hRP hb hblow
      compat t ht
    finite_end_slab := TerminalRestart.finite_end_slab I C O W hC hRP hb hblow compat
  }⟩⟩
  constructor
  · intro h
    exact (hcoreNe.ne_empty h).elim
  · intro h
    let := h
    exact (isEmptyElim (Classical.choice hpost))

end PoincareConjecture.RepairedContinuationLimitBridge
