import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.EndCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.OrientedSelection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.SelectedGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.DisjointCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B in
theorem continuation_of_calibrated_horns (P : M33Predecessors.{u})
    (hcoreNe : I.controlled_core.Nonempty)
    (hhorns : ∀ K : TerminalComponentPath N.limit.extension,
      (K.component ∩ {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K,
        ∃ horn : StrongHorn N.limit.extension (terminalAccuracyFactor * H.epsilon),
          HornBoundaryBelow horn (I.rho / (2 * H.constant)) ∧
          (∀ x ∈ horn.boundary_sphere,
            (N.limit.extension.extended.connection T).scalarCurvature x <
              32 * H.constant * I.rho⁻¹ ^ 2) ∧
          horn.carrier ⊆ K.component ∧
          Disjoint horn.carrier
            {x | (N.limit.extension.extended.connection T).scalarCurvature x ≤ I.rho⁻¹ ^ 2} ∧
          ∃ n, Subtype.val '' e.tail n ⊆ horn.carrier) :
    Nonempty (RepairedBranchContinuationData I) := by
  classical
  let ι := Σ K : {K : TerminalComponentPath N.limit.extension //
      (K.component ∩ {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2}).Nonempty},
    TerminalEnd K.val
  have hchoices := fun i : ι => hhorns i.1.val i.1.property i.2
  choose horn hboundary hlinear hcomponent hlow n hn using hchoices
  have hcutchoices := fun i : ι => B.exists_oriented_terminal_cut (horn i) (hboundary i)
  choose ν hcenter hcarrier hscalar hornCuts cuts htail using hcutchoices
  have hcore (i : ι) : (ν i).center ∈
      SurgeryTerminalCoreComponents (N.limit.extension.extended.connection T) I.rho := by
    obtain ⟨p, hp, hplow⟩ := i.1.property
    refine ⟨p, ?_, ?_⟩
    · simpa only [mem_setOf_eq, N.limit.terminal_scalar_eq] using hplow
    · have hc := hcomponent i (hcenter i)
      rw [i.1.val.component_eq] at hp hc
      exact (connectedComponent_eq hp) ▸ hc
  have hcover : ∀ K : TerminalComponentPath N.limit.extension,
      (K.component ∩ {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ (cuts i).tail := by
    intro K hK e
    let i : ι := ⟨⟨K, hK⟩, e⟩
    obtain ⟨m, _, hm⟩ := e.exists_tail_subset_hornEndCut (hornCuts i) (n i) (hn i)
    exact ⟨i, m, (htail i).symm ▸ hm⟩
  have hδ : F.parameters.delta T ≤ 1 / 200 :=
    (I.terminal_delta_bound.trans_lt F.local_constants.delta₀_lt).le
  have hhC : F.parameters.h T ≤ I.rho / (2 * H.constant) := by
    rw [B.parameter_constant_eq]
    exact I.terminal_height_rho_constant
  obtain ⟨s, hsneck, hstails, _, hscover⟩ := N.limit.exists_finite_disjoint_end_cut_cover
    ν horn hδ I.terminal_delta_lt_half hornCuts cuts htail I.rho_pos B.constant_one_le
    (F.parameters.h_pos T I.terminal_pos.le) I.terminal_height_rho_delta hhC
    hscalar hlinear hcarrier hcore hlow hcover
  let J : s → MetricSurgeryInput F.local_constants (N.limit.extension.extended.metric T) :=
    fun i => I.terminalSurgeryInput N.limit.extension (ν i.val) (hscalar i.val)
      (Surgery.Terminal.terminal_pinched H N.limit)
  let R : ∀ i : s, MetricSurgeryResult F.standard_initial (J i) :=
    fun i => Classical.choice (B.surgery_operation (J i))
  have hneck : Pairwise (fun i j : s => Disjoint (J i).neck.carrier (J j).neck.carrier) :=
    fun i j hij => hsneck i.property j.property (fun h => hij (Subtype.ext h))
  have htails : Pairwise (fun i j : s => Disjoint (cuts i.val).tail (cuts j.val).tail) :=
    fun i j hij => hstails i.property j.property (fun h => hij (Subtype.ext h))
  have hcutslow (i : s) : Disjoint (cuts i.val).tail
      {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} := by
    rw [htail i.val]
    simpa only [N.limit.terminal_scalar_eq] using (hornCuts i.val).disjoint_low_curvature
  have hspherelow (i : s) : Disjoint (J i).neck.central_sphere
      {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} := by
    change Disjoint (ν i.val).central_sphere
      {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2}
    have hd := (I.selected_neck_disjoint_low_core (ν i.val) (hscalar i.val)).mono_left
      (ν i.val).central_sphere_subset
    simpa only [N.limit.terminal_scalar_eq] using hd
  have hcover' : ∀ K : TerminalComponentPath N.limit.extension,
      (K.component ∩ {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i : s, ∃ m, Subtype.val '' e.tail m ⊆ (cuts i.val).tail := by
    intro K hK e
    obtain ⟨i, hi, m, hm⟩ := hscover K hK e
    exact ⟨⟨i, hi⟩, m, hm⟩
  exact B.continuation_of_finite_end_cover P J R (fun i => cuts i.val) hneck htails
    (fun i => hcore i.val) hcutslow hspherelow hcover' (fun _ => rfl) (fun _ => rfl)
    (fun i => I.selected_neck_scale (ν i.val) (hscalar i.val)) hcoreNe
    (fun i => ν i.val) (fun _ => rfl)

end PoincareConjecture.RepairedContinuationLimitBridge
