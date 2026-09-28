import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.StrongBoundary.GluingWorldlines
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.StrongBoundary.HistoryCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.PreFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial

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
  (K : TerminalStrongNeck N.limit.extension (F.parameters.delta T))

theorem terminalNeck_old_time (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0) :
    T + s / (K.scale⁻¹ ^ 2) ∈ G.interval := by
  have hm := N.limit.extension.times_subset
    (K.time_cylinder.time_mem_of_nonempty_source ⟨K.center⟩ s ⟨hs.1, hs.2.le⟩)
  exact hm.resolve_right (by
    have hh := div_neg_of_neg_of_pos hs.2 K.time_cylinder.scale_pos
    simp only [mem_singleton_iff]
    linarith)

def terminalNeckOldCylinder : GeneralizedFlowCylinder G
    (N.limit.extension.extended.slice T) T (K.scale⁻¹ ^ 2) (Ioo (-1 : ℝ) 0) K.carrier :=
  N.limit.extension.pullCylinder
    (K.time_cylinder.restrictTime (show Ioo (-1 : ℝ) 0 ⊆ Ioc (-1 : ℝ) 0 from
      fun _ hs => ⟨hs.1, hs.2.le⟩)) (terminalNeck_old_time K)

def terminalNeckCylinder : SurgeryFlowCylinder F (N.limit.extension.extended.slice T)
    T (K.scale⁻¹ ^ 2) (Ioo (-1 : ℝ) 0) K.carrier :=
  B.history.toSurgeryOpenCylinder I.last_slab.regularHistoryWindow
    (Subset.antisymm H.interval_preterminal H.interval_exhausts_preterminal)
    (terminalNeckOldCylinder K) ordConnected_Ioo isOpen_Ioo (terminalNeck_old_time K)

theorem terminalNeckCylinder_forward (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    (x : (N.limit.extension.extended.slice T).carrier) :
    (B.terminalNeckCylinder K).forward s hs x =
      B.history.forward (T + s / (K.scale⁻¹ ^ 2)) (terminalNeck_old_time K s hs)
        (N.limit.extension.inverse _ (terminalNeck_old_time K s hs)
          (K.time_cylinder.forward s ⟨hs.1, hs.2.le⟩ x)) := rfl

theorem terminalNeckCylinder_pullbackInner (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    (x : (N.limit.extension.extended.slice T).carrier) (hx : x ∈ K.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (B.terminalNeckCylinder K).pullbackInner s hs x v w =
      K.time_cylinder.pullbackInner s ⟨hs.1, hs.2.le⟩ x v w := by
  exact (B.history.toSurgeryOpenCylinder_pullbackInner I.last_slab.regularHistoryWindow
    (Subset.antisymm H.interval_preterminal H.interval_exhausts_preterminal)
    (terminalNeckOldCylinder K) ordConnected_Ioo isOpen_Ioo (terminalNeck_old_time K)
    K.carrier_open s hs x hx v w).trans
      (N.limit.extension.pullCylinder_pullbackInner _ (terminalNeck_old_time K)
        K.carrier_open s hs x hx v w)

theorem terminalNeckCylinder_reference (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    (ht : T + s / (K.scale⁻¹ ^ 2) ∈ Ico H.reference.tMinus T)
    (x : (N.limit.extension.extended.slice T).carrier) (hx : x ∈ K.carrier) :
    (B.terminalNeckCylinder K).forward s hs x =
      (B.reference_identify ⟨T + s / (K.scale⁻¹ ^ 2), ht⟩).symm (N.limit.terminal_source x) := by
  rw [B.terminalNeckCylinder_forward,
    N.limit.strongNeck_inverse_reference K x hx s hs ht]
  exact B.history_reference ⟨T + s / (K.scale⁻¹ ^ 2), ht⟩ (N.limit.terminal_source x)

theorem terminalNeckCylinder_comparison :
    RoundCylinderFamilyClose (F.parameters.delta T) (Ioc (-1 : ℝ) 0)
      (fun s => if s = 0 then fun z v w => K.scale⁻¹ ^ 2 *
          roundCylinderPullback (N.limit.extension.extended.metric T) K.coordinate_map z v w
        else surgeryCylinderPullback (B.terminalNeckCylinder K) K.coordinate_map s) := by
  apply RoundCylinderFamilyClose.congr
    (B' := generalizedCylinderPullback K.time_cylinder K.coordinate_map) ?_ K.metric_comparison
  intro s hs z hz v w
  by_cases hzero : s = 0
  · subst s
    rw [if_pos rfl]
    exact (K.pullback_zero hz v w).symm
  · have hsi : s ∈ Ioo (-1 : ℝ) 0 := ⟨hs.1, lt_of_le_of_ne hs.2 hzero⟩
    have hcoord : K.coordinate_map z ∈ K.carrier := by
      have h := (K.coordinate (z.1, ⟨z.2, hz⟩)).property
      rwa [K.coordinate_map_eq] at h
    simp only [if_neg hzero, surgeryCylinderPullback, dif_pos hsi,
      generalizedCylinderPullback, dif_pos hs]
    exact B.terminalNeckCylinder_pullbackInner K s hsi _ hcoord _ _

theorem referenceIdentify_rebase (sigma : Ico H.reference.tMinus T)
    (t : Ico sigma.val T) (x : M) :
    (B.reference_identify
      ⟨t.val, sigma.property.1.trans t.property.1, t.property.2⟩).symm x =
      I.last_slab.rebaseIdentify
        ⟨sigma.val, B.reference_start_lt.le.trans sigma.property.1, sigma.property.2⟩ t
        ((B.reference_identify sigma).symm x) := by
  let r : Ico I.last_slab.start T :=
    ⟨sigma.val, B.reference_start_lt.le.trans sigma.property.1, sigma.property.2⟩
  let y := (I.last_slab.identify r).symm ((B.reference_identify sigma).symm x)
  have hs := B.core_map_eq_reference_at sigma y
  have ht := B.core_map_eq_reference_at
    ⟨t.val, sigma.property.1.trans t.property.1, t.property.2⟩ y
  have hs' : B.core_map y = x := by
    simpa only [y, r, Diffeomorph.apply_symm_apply] using hs
  apply (B.reference_identify
    ⟨t.val, sigma.property.1.trans t.property.1, t.property.2⟩).injective
  exact ((B.reference_identify
    ⟨t.val, sigma.property.1.trans t.property.1, t.property.2⟩).apply_symm_apply x).trans
      (hs'.symm.trans ht)

theorem terminalNeckCylinder_rebase_reference (sigma : Ico H.reference.tMinus T)
    (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    (ht : T + s / (K.scale⁻¹ ^ 2) ∈ Ico sigma.val T)
    (x : (N.limit.extension.extended.slice T).carrier) (hx : x ∈ K.carrier) :
    (B.terminalNeckCylinder K).forward s hs x =
      I.last_slab.rebaseIdentify
        ⟨sigma.val, B.reference_start_lt.le.trans sigma.property.1, sigma.property.2⟩
        ⟨T + s / (K.scale⁻¹ ^ 2), ht⟩
        ((B.reference_identify sigma).symm (N.limit.terminal_source x)) :=
  (B.terminalNeckCylinder_reference K s hs ⟨sigma.property.1.trans ht.1, ht.2⟩ x hx).trans
    (B.referenceIdentify_rebase sigma ⟨_, ht⟩ _)

end PoincareConjecture.RepairedContinuationLimitBridge
