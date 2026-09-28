import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitReference




noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationInput

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)

def lateReferenceTime (a : ℝ) (ha : a < T) : Ico a T := by
  let s := (max a (T - F.parameters.h T ^ 2) + T) / 2
  have hh : 0 < F.parameters.h T ^ 2 := sq_pos_of_pos (F.parameters.h_pos T I.terminal_pos.le)
  have hm : max a (T - F.parameters.h T ^ 2) < T := max_lt ha (by linarith)
  exact ⟨s, by dsimp [s]; linarith [le_max_left a (T - F.parameters.h T ^ 2)],
    by dsimp [s]; linarith⟩

theorem lateReferenceTime_close (a : ℝ) (ha : a < T) :
    T - F.parameters.h T ^ 2 < (I.lateReferenceTime a ha).1 := by
  have hh : 0 < F.parameters.h T ^ 2 := sq_pos_of_pos (F.parameters.h_pos T I.terminal_pos.le)
  have hm : max a (T - F.parameters.h T ^ 2) < T := max_lt ha (by linarith)
  dsimp [lateReferenceTime]
  linarith [le_max_right a (T - F.parameters.h T ^ 2)]

end PoincareConjecture.RepairedContinuationInput

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

theorem controlled_core_regular :
    I.controlled_core ⊆ B.core_map ⁻¹' H.reference.regularLimitSet := by
  intro x hx
  exact (B.core_map_image.subset (mem_image_of_mem _ hx)).1

theorem controlled_core_terminal_scalar
    [Nonempty (N.limit.extension.extended.slice T).carrier]
    {x : (F.slice I.last_slab.start).carrier} (hx : x ∈ I.controlled_core) :
    (N.limit.extension.extended.connection T).scalarCurvature
      (N.limit.sourceInverse (B.core_map x)) ≤ I.rho⁻¹ ^ 2 := by
  obtain ⟨_, z, hz, hscalar⟩ := B.core_map_image.subset (mem_image_of_mem _ hx)
  rw [← hz, N.limit.sourceInverse_source, ← N.limit.terminal_scalar_eq]
  exact hscalar

end PoincareConjecture.RepairedContinuationLimitBridge
