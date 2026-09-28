import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.AssemblyProperties
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.StrongBoundary.RestartCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.StrongBoundary
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

local notation "C" => cutCarrier J R U hU hd hc

local instance : Nonempty (C).carrier := cutCarrier_nonempty J R U hU hd hc

variable {lifetime : ℝ≥0∞}
  (O : RicciFlow 3 (cutCarrier J R U hU hd hc).carrier
    {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < lifetime})
  (hPost : (⟨cutCarrier J R U hU hd hc, cutMetric J R U hU hd hc⟩ : SliceMetric.{u}) =
    Splice.family F T (cutCarrier J R U hU hd hc) O T)

local notation "E" => B.assembleNonemptyEvent σ hclose J R U hU hd hc hneck hUn hfront
  hcompact hcore htime hdelta hscale (Splice.family F T C O)
  (fun t ht => Eq.symm (Splice.family_before F T C O ht)) hPost

theorem assembleNonemptyEvent_slab_compatibility (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < lifetime})
    (hfree : Disjoint (Splice.eventTimes F T) (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico σ.1 T) (ht' : t ∈ Ico σ.1 T)
    (x : (Splice.slice F T C O σ.1).carrier) :
    (Splice.regularSlab F T C O I.time_domain_eq hab hJ hfree).transport
      ⟨s, hs⟩ ⟨t, ht⟩ ((E).pre_identify ⟨s, hs'⟩ x) =
        (E).pre_identify ⟨t, ht'⟩ x := by
  have hb : b < T := (Splice.slab_side F T hfree).resolve_right
    (fun ha => (not_lt_of_ge (ha.trans hs.1)) hs'.2)
  have hold : Icc a b ⊆ F.time_domain := by
    intro q hq
    rw [I.time_domain_eq]
    exact ⟨(hJ hq).1, hq.2.trans_lt hb⟩
  have hfreeold := hfree.mono_left (subset_insert T F.surgery_times)
  obtain ⟨y, rfl⟩ := (identify _ _ (Splice.family_before F T C O σ.2.2).symm).surjective x
  have hident (q : Ico σ.1 T) :=
    B.assembleNonemptyEvent_pre_identify σ hclose J R U hU hd hc hneck hUn hfront
      hcompact hcore htime hdelta hscale (Splice.family F T C O)
      (fun _ ht => (Splice.family_before F T C O ht).symm) hPost q y
  exact (congrArg ((Splice.regularSlab F T C O I.time_domain_eq hab hJ hfree).transport
    ⟨s, hs⟩ ⟨t, ht⟩) (hident ⟨s, hs'⟩)).trans
    ((Splice.regularSlab_transport_before F T C O I.time_domain_eq hab hJ hfree
      hb hold hfreeold ⟨s, hs⟩ ⟨t, ht⟩
      (I.last_slab.rebaseIdentify (B.referenceRebaseTime σ) ⟨s, hs'⟩ y)).trans
      ((congrArg (Splice.identifyBefore F T C O t ht'.2)
        (I.last_slab.rebase_transport (B.referenceRebaseTime σ) a b hab hold hfreeold
          s t hs ht hs' ht' y)).trans (hident ⟨t, ht'⟩).symm))

variable (hC : IsCompact (univ : Set (cutCarrier J R U hU hd hc).carrier))
  (hRP : SurgeryNoTwoSidedProjectivePlane (cutCarrier J R U hU hd hc))
  (hB : ENNReal.ofReal T < lifetime)
  (hblow : lifetime ≠ ⊤ → ∀ a s : ℝ, s < lifetime.toReal →
    ∃ t ∈ Ioo (max T s) lifetime.toReal, ∃ x : (cutCarrier J R U hU hd hc).carrier,
      a < (O.connection t).curvatureTensorNorm x)

local notation "compat" => B.assembleNonemptyEvent_slab_compatibility σ hclose J R U hU hd hc
  hneck hUn hfront hcompact hcore htime hdelta hscale O hPost
local notation "K" => TerminalRestart.canonicalNonemptyEvent I C O E
local notation "A" => TerminalRestart.extension I C O K hC hRP hB hblow compat

set_option maxHeartbeats 800000 in
theorem assembled_terminal_strong_boundaries
    [Nonempty ((A).extended.slice T).carrier]
    (ν : ι → TerminalStrongNeck N.limit.extension (F.parameters.delta T))
    (hJneck : ∀ i, (J i).neck = (ν i).spatialNeck
      ((hdelta i) ▸ (J i).neck.epsilon_lt_half))
    (hT : T ∈ (A).extended.surgery_times) :
    ∀ i, Nonempty (SurgeryTerminalStrongNeck (A).extended T hT i) := by
  have heq : K = (A).extended.event T hT :=
    (TerminalRestart.event_terminal I C O K hT).symm
  have hcount := congrArg (fun evt => evt.cap_count) heq
  intro j
  let i : Fin (Fintype.card ι) := Fin.cast hcount.symm j
  let k := (Fintype.equivFin ι).symm i
  have hdata : ∃ cylinder : SurgeryFlowCylinder (A).extended
      (N.limit.extension.extended.slice T) T ((J k).neck.scale⁻¹ ^ 2)
      (Ioo (-1 : ℝ) 0) (J k).neck.carrier,
      (∀ s hs, ∀ ht : T + s / (J k).neck.scale⁻¹ ^ 2 ∈ Ico σ.1 T,
        ∀ x ∈ (J k).neck.carrier,
          cylinder.forward s hs x = (E).pre_identify
            ⟨T + s / (J k).neck.scale⁻¹ ^ 2, ht⟩ ((E).limit_identify.inverse x)) ∧
      RoundCylinderFamilyClose ((A).extended.parameters.delta T) (Ioc (-1 : ℝ) 0)
        (fun s => if s = 0 then fun z v w => (J k).neck.scale⁻¹ ^ 2 *
          roundCylinderPullback (N.limit.extension.extended.metric T)
            (J k).neck.coordinate_map z v w
        else surgeryCylinderPullback cylinder (J k).neck.coordinate_map s) := by
    rw [hJneck k]
    refine ⟨B.restartedTerminalNeckCylinder (ν k) A, ?_,
      B.restartedTerminalNeckCylinder_comparison (ν k) A⟩
    intro s hs ht x hx
    exact (B.restartedTerminalNeckCylinder_reference (ν k) A σ s hs ht x hx).trans
      (B.assembleNonemptyEvent_pre_identify_limit_inverse σ hclose J R U hU hd hc
        hneck hUn hfront hcompact hcore htime hdelta hscale (Splice.family F T C O)
        (fun t ht => (Splice.family_before F T C O ht).symm) hPost ⟨_, ht⟩ x).symm
  obtain ⟨cylinder, href, hcomp⟩ := hdata
  have hi : Nonempty (SurgeryTerminalStrongNeck (A).extended T hT (Fin.cast hcount i)) :=
    ⟨@TerminalRestart.strongNeckOfEvent (A).extended T hT inferInstance
      K heq i cylinder href hcomp⟩
  simpa only [i, Fin.cast_cast, Fin.cast_refl, id_eq] using hi

end PoincareConjecture.RepairedContinuationLimitBridge
