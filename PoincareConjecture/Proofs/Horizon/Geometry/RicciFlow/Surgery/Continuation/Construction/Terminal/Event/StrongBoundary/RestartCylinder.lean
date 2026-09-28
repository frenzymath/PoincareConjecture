import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.StrongBoundary.TerminalCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.ExtensionCylinderMetric








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
  (A : SurgeryFlowExtension F)

def restartedTerminalNeckCylinder : SurgeryFlowCylinder A.extended
    (N.limit.extension.extended.slice T) T (K.scale⁻¹ ^ 2) (Ioo (-1 : ℝ) 0) K.carrier :=
  A.pushCylinder (B.terminalNeckCylinder K)

theorem restartedTerminalNeckCylinder_pullbackInner
    (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    (x : (N.limit.extension.extended.slice T).carrier) (hx : x ∈ K.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (B.restartedTerminalNeckCylinder K A).pullbackInner s hs x v w =
      K.time_cylinder.pullbackInner s ⟨hs.1, hs.2.le⟩ x v w :=
  (A.pushCylinder_pullbackInner (B.terminalNeckCylinder K) K.carrier_open s hs x hx v w).trans
    (B.terminalNeckCylinder_pullbackInner K s hs x hx v w)

theorem restartedTerminalNeckCylinder_reference (sigma : Ico H.reference.tMinus T)
    (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    (ht : T + s / (K.scale⁻¹ ^ 2) ∈ Ico sigma.val T)
    (x : (N.limit.extension.extended.slice T).carrier) (hx : x ∈ K.carrier) :
    (B.restartedTerminalNeckCylinder K A).forward s hs x =
      A.identify (T + s / (K.scale⁻¹ ^ 2))
        ((B.terminalNeckCylinder K).time_subset ⟨s, hs, rfl⟩)
        (I.last_slab.rebaseIdentify
          ⟨sigma.val, B.reference_start_lt.le.trans sigma.property.1, sigma.property.2⟩
          ⟨T + s / (K.scale⁻¹ ^ 2), ht⟩
          ((B.reference_identify sigma).symm (N.limit.terminal_source x))) :=
  congrArg (A.identify _ ((B.terminalNeckCylinder K).time_subset ⟨s, hs, rfl⟩))
    (B.terminalNeckCylinder_rebase_reference K sigma s hs ht x hx)

theorem restartedTerminalNeckCylinder_comparison :
    RoundCylinderFamilyClose (A.extended.parameters.delta T) (Ioc (-1 : ℝ) 0)
      (fun s => if s = 0 then fun z v w => K.scale⁻¹ ^ 2 *
          roundCylinderPullback (N.limit.extension.extended.metric T) K.coordinate_map z v w
        else surgeryCylinderPullback (B.restartedTerminalNeckCylinder K A) K.coordinate_map s) := by
  rw [A.parameters_eq]
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
    exact B.restartedTerminalNeckCylinder_pullbackInner K A s hsi _ hcoord _ _

end PoincareConjecture.RepairedContinuationLimitBridge
