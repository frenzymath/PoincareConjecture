import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Admissible
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Properties

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

open Surgery.Extinction

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)
  (hempty : I.controlled_core = ∅)

def extinctionExtension : SurgeryFlowExtension F :=
  extension I
    (canonicalVanishingEvent I (B.vanishingEvent hempty))
    (B.vanishingEvent_slab_compatibility hempty)

theorem extinction_surgery_at_terminal :
    T ∈ (B.extinctionExtension hempty).extended.surgery_times :=
  mem_insert _ _

theorem extinction_terminal_empty :
    IsEmpty ((B.extinctionExtension hempty).extended.slice T).carrier :=
  slice_empty_after F T le_rfl

def extinctionOperation : RepairedVanishingTerminalOperationCertificate I
    (B.extinctionExtension hempty)
    (B.extinction_surgery_at_terminal hempty)
    (B.extinction_terminal_empty hempty) := by
  let V := B.vanishingEvent hempty
  let V' := canonicalVanishingEvent I V
  let hV := B.vanishingEvent_slab_compatibility hempty
  let E := extension I V' hV
  let r := I.vanishingReferenceTime
  let f := I.last_slab.identify r
  let e := Surgery.Splice.identifyBefore F T (emptyCarrier (F.slice 0))
    (emptyFlow (F.metric 0) T) r.1 r.2.2
  let d := f.trans e
  let W := Surgery.Splice.vanishingEvent F T (emptyCarrier (F.slice 0))
    (emptyFlow (F.metric 0) T) V'
  let : IsEmpty (E.extended.slice T).carrier := slice_empty_after F T le_rfl
  refine {
    reference_time := r.1
    reference_mem := r.2
    reference_h := F.parameters.h T
    reference_h_pos := F.parameters.h_pos T I.terminal_pos.le
    reference_h_eq := rfl
    reference_close := I.vanishingReference_bounds.2.2
    event := W
    event_eq := rfl
    terminal_policy := ?_
    event_tMinus_mem := I.last_slab.time_subset r.2
    event_tMinus_slab_mem := r.2
    event_tMinus_eq_reference := rfl
    reference_identify := d
    reference_identify_eq := fun _ => rfl
    core_empty := hempty
    source_to_pre := d
    source_to_pre_eq := fun _ => rfl
    reference_identify_eq_source := fun _ => rfl
    pre_identify_transport := ?_
    pre_flow_metric_transport := ?_
    disappearing_cover_rebased := fun t x => W.disappearing_cover t.1 t.2 (d x)
    no_later_surgery := fun s hs _ => no_later_surgery I V' hV s hs }
  · exact V'.copyBefore_terminalPolicy
      (past := fun q => ⟨F.slice q, F.metric q⟩)
      (future := Surgery.Splice.family F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T))
      (fun _q hq => (Surgery.Splice.family_before F T (emptyCarrier (F.slice 0))
        (emptyFlow (F.metric 0) T) hq.2).symm)
      (canonicalVanishingEvent_terminalPolicy I V
        (B.vanishingEvent_terminalPolicy hempty))
  · intro t htF htS x
    exact (Surgery.Splice.vanishingEvent_pre_identify F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) V' t (f x)).trans
        (congrArg (E.identify t.1 htF) (I.last_slab.rebaseIdentify_source r t x))
  · intro t x v w
    change (W.pre_flow.metric t.1).inner (e (f x))
      (mfderiv (𝓡 3) (𝓡 3) (e ∘ f) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e ∘ f) x w) = _
    rw [mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) _)
      (f.contMDiff.mdifferentiable (by simp) _)]
    exact (V'.copyBefore_pre_flow_inner
      (past := fun q => ⟨F.slice q, F.metric q⟩)
      (future := Surgery.Splice.family F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T))
      (fun _q hq => (Surgery.Splice.family_before F T (emptyCarrier (F.slice 0))
        (emptyFlow (F.metric 0) T) hq.2).symm)
      t.1 (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)).trans
        (I.last_slab.rebaseFlow_source_metric r t.1 x v w)

end PoincareConjecture.RepairedContinuationLimitBridge
