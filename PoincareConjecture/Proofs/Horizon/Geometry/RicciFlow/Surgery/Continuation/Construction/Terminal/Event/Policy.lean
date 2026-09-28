import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.AssemblyProperties
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Policy

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

open Surgery.Terminal.Gluing SurgeryEventRebuild

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
  (future : ℝ → SliceMetric.{u})
  (hPast : ∀ t, t < T → (⟨F.slice t, F.metric t⟩ : SliceMetric.{u}) = future t)
  (hPost : (⟨cutCarrier J R U hU hd hc, cutMetric J R U hU hd hc⟩ : SliceMetric.{u}) =
    future T)

local notation "E" => B.assembleNonemptyEvent σ hclose J R U hU hd hc hneck hUn hfront
  hcompact hcore htime hdelta hscale future hPast hPost

def assembleNonemptyEvent_terminalPolicy
    (cuts : ∀ i, SurgeryEndCut (J i).neck)
    (hretained : closure (U : Set (N.limit.extension.extended.slice T).carrier) =
      SurgeryTerminalCoreComponents (N.limit.extension.extended.connection T) I.rho \
        ⋃ i, (cuts i).tail) : SurgeryEventTerminalPolicy (E) where
  cuts i := cuts ((Fintype.equivFin ι).symm i)
  retained_eq := by
    rw [B.assembleNonemptyEvent_retained_image]
    change closure (U : Set (N.limit.extension.extended.slice T).carrier) =
      SurgeryTerminalCoreComponents (N.limit.extension.extended.connection T)
        (F.parameters.delta T * F.parameters.r T) \
          ⋃ i : Fin (Fintype.card ι), (cuts ((Fintype.equivFin ι).symm i)).tail
    have hunion : (⋃ i : Fin (Fintype.card ι),
        (cuts ((Fintype.equivFin ι).symm i)).tail) = ⋃ i, (cuts i).tail :=
      (Fintype.equivFin ι).symm.surjective.iUnion_comp (fun i => (cuts i).tail)
    rw [hunion, ← I.rho_eq]
    exact hretained

end PoincareConjecture.RepairedContinuationLimitBridge
