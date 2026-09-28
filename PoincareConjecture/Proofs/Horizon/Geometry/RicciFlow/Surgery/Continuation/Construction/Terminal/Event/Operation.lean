import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Policy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.StrongBoundary.Assembled
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.CanonicalTail









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
  {lifetime : ℝ≥0∞}
  (O : RicciFlow 3 (cutCarrier J R U hU hd hc).carrier
    {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < lifetime})
  (hPost : (⟨cutCarrier J R U hU hd hc, cutMetric J R U hU hd hc⟩ : SliceMetric.{u}) =
    Splice.family F T (cutCarrier J R U hU hd hc) O T)

local notation "cutSlice" => cutCarrier J R U hU hd hc
local notation "E" => B.assembleNonemptyEvent σ hclose J R U hU hd hc hneck hUn hfront
  hcompact hcore htime hdelta hscale (Splice.family F T cutSlice O)
  (fun t ht => Eq.symm (Splice.family_before F T cutSlice O ht)) hPost
local notation "W" => TerminalRestart.canonicalNonemptyEvent I cutSlice O E

local instance : Nonempty (cutSlice).carrier := cutCarrier_nonempty J R U hU hd hc

variable (hC : IsCompact (univ : Set (cutCarrier J R U hU hd hc).carrier))
  (hRP : SurgeryNoTwoSidedProjectivePlane (cutCarrier J R U hU hd hc))
  (hB : ENNReal.ofReal T < lifetime)
  (hblow : lifetime ≠ ⊤ → ∀ a s : ℝ, s < lifetime.toReal →
    ∃ t ∈ Ioo (max T s) lifetime.toReal, ∃ x : (cutCarrier J R U hU hd hc).carrier,
      a < (O.connection t).curvatureTensorNorm x)

local notation "compat" => B.assembleNonemptyEvent_slab_compatibility σ hclose J R U hU hd hc
  hneck hUn hfront hcompact hcore htime hdelta hscale O hPost
local notation "A" => TerminalRestart.extension I cutSlice O W hC hRP hB hblow compat

local instance : Nonempty ((A).extended.slice T).carrier :=
  TerminalRestart.slices_nonempty I cutSlice O T I.terminal_pos.le

set_option maxHeartbeats 800000 in
def assembledNonemptyOperation
    (cuts : ∀ i, SurgeryEndCut (J i).neck)
    (hretained : closure (U : Set (N.limit.extension.extended.slice T).carrier) =
      SurgeryTerminalCoreComponents (N.limit.extension.extended.connection T) I.rho \
        ⋃ i, (cuts i).tail)
    (hcoreNe : I.controlled_core.Nonempty)
    (hT : T ∈ (A).extended.surgery_times) :
    RepairedNonemptyTerminalOperationCertificate I A hT inferInstance := by
  let r := B.referenceRebaseTime σ
  let f := I.last_slab.identify r
  let e := Splice.identifyBefore F T cutSlice O σ.1 σ.2.2
  let d := f.trans e
  letI : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
  refine {
    reference_time := σ.1
    reference_mem := r.2
    reference_h := F.parameters.h T
    reference_h_pos := F.parameters.h_pos T I.terminal_pos.le
    reference_h_eq := rfl
    reference_close := hclose
    event := W
    event_eq := (TerminalRestart.event_terminal I cutSlice O W hT).symm
    terminal_policy := TerminalRestart.canonicalNonemptyEvent_terminalPolicy I cutSlice O E
      (B.assembleNonemptyEvent_terminalPolicy σ hclose J R U hU hd hc hneck hUn hfront
        hcompact hcore htime hdelta hscale (Splice.family F T cutSlice O)
        (fun t ht => (Splice.family_before F T cutSlice O ht).symm) hPost cuts hretained)
    event_tMinus_mem := I.last_slab.time_subset r.2
    event_tMinus_slab_mem := r.2
    event_tMinus_eq_reference := rfl
    reference_identify := d
    reference_identify_eq := fun _ => rfl
    retained_post := (W).retained_post
    retained_post_eq := rfl
    core_nonempty := hcoreNe
    source_to_pre := d
    source_to_pre_eq := fun _ => rfl
    reference_identify_eq_source := fun _ => rfl
    pre_identify_transport := ?_
    regular_limit_source := B.core_map ⁻¹' H.reference.regularLimitSet
    regular_limit_transport := ?_
    controlled_core_subset_regular_limit := B.controlled_core_regular
    controlled_core_threshold := ?_
    pre_flow_metric_transport := ?_
    disappearing_cover_rebased := fun t x hx => (W).disappearing_cover t.1 t.2 (d x) hx }
  · intro t htF htS x
    exact (B.assembleNonemptyEvent_pre_identify σ hclose J R U hU hd hc hneck hUn hfront
      hcompact hcore htime hdelta hscale (Splice.family F T cutSlice O)
      (fun t ht => (Splice.family_before F T cutSlice O ht).symm) hPost t (f x)).trans
        (congrArg ((A).identify t.1 htF) (I.last_slab.rebaseIdentify_source r t x))
  · change relabel (C := fun p => Set p.1.carrier)
      (Splice.family_before F T cutSlice O σ.2.2).symm
      (B.reference_identify σ ⁻¹' H.reference.regularLimitSet) =
        d '' (B.core_map ⁻¹' H.reference.regularLimitSet)
    rw [← relabel_set_image]
    have hsource : f '' (B.core_map ⁻¹' H.reference.regularLimitSet) =
        B.reference_identify σ ⁻¹' H.reference.regularLimitSet := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change B.reference_identify σ (f x) ∈ H.reference.regularLimitSet
        have hid : B.core_map x = B.reference_identify σ (f x) :=
          B.core_map_eq_reference_at σ x
        exact hid ▸ hx
      · intro hy
        refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
        change B.core_map (f.symm y) ∈ H.reference.regularLimitSet
        have hid : B.core_map (f.symm y) = B.reference_identify σ (f (f.symm y)) :=
          B.core_map_eq_reference_at σ (f.symm y)
        rw [hid, f.apply_symm_apply]
        exact hy
    change e '' (B.reference_identify σ ⁻¹' H.reference.regularLimitSet) =
      (e ∘ f) '' (B.core_map ⁻¹' H.reference.regularLimitSet)
    rw [image_comp, hsource]
  · intro x hx
    change (N.limit.extension.extended.connection T).scalarCurvature
      ((E).limit_identify.map (e (f x))) ≤ I.rho⁻¹ ^ 2
    have hmap := B.assembleNonemptyEvent_source_map σ hclose J R U hU hd hc hneck hUn hfront
      hcompact hcore htime hdelta hscale (Splice.family F T cutSlice O)
      (fun t ht => (Splice.family_before F T cutSlice O ht).symm) hPost x
    exact (congrArg (N.limit.extension.extended.connection T).scalarCurvature hmap).trans_le
      (B.controlled_core_terminal_scalar hx)
  · intro t x v w
    exact B.assembleNonemptyEvent_source_metric σ hclose J R U hU hd hc hneck hUn hfront
      hcompact hcore htime hdelta hscale (Splice.family F T cutSlice O)
      (fun t ht => (Splice.family_before F T cutSlice O ht).symm) hPost t.1 x v w

end PoincareConjecture.RepairedContinuationLimitBridge
