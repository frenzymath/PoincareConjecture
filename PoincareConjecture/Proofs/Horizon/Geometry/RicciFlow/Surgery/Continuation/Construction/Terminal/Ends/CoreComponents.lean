import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CanonicalCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Components
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.TerminalPolicy
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (rho : ℝ)

theorem SurgeryTerminalCoreComponents.low_subset :
    {x | D.scalarCurvature x ≤ rho⁻¹ ^ 2} ⊆ SurgeryTerminalCoreComponents D rho :=
  fun x hx => ⟨x, hx, mem_connectedComponent⟩

theorem SurgeryTerminalCoreComponents.component_subset {x : M}
    (hx : x ∈ SurgeryTerminalCoreComponents D rho) :
    connectedComponent x ⊆ SurgeryTerminalCoreComponents D rho := by
  obtain ⟨y, hy, hxy⟩ := hx
  intro z hz
  exact ⟨y, hy, (connectedComponent_eq hxy).symm ▸ hz⟩

theorem SurgeryTerminalCoreComponents.isClopen :
    IsClopen (SurgeryTerminalCoreComponents D rho) := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  have hopen : IsOpen (SurgeryTerminalCoreComponents D rho) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.mem_of_superset (isOpen_connectedComponent.mem_nhds mem_connectedComponent)
      (SurgeryTerminalCoreComponents.component_subset D rho hx)
  refine ⟨isOpen_compl_iff.mp ?_, hopen⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  apply Filter.mem_of_superset (isOpen_connectedComponent.mem_nhds mem_connectedComponent)
  intro y hy hycore
  apply hx
  apply SurgeryTerminalCoreComponents.component_subset D rho hycore
  rw [← connectedComponent_eq hy]
  exact mem_connectedComponent

theorem SurgeryTerminalCoreComponents.exists_finite_components
    (hcompact : IsCompact {x | D.scalarCurvature x ≤ rho⁻¹ ^ 2}) :
    ∃ points : Finset M,
      (∀ x ∈ points, D.scalarCurvature x ≤ rho⁻¹ ^ 2) ∧
      SurgeryTerminalCoreComponents D rho = ⋃ x ∈ points, connectedComponent x := by
  classical
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨s, hs, hcover⟩ := Surgery.Terminal.exists_finset_component_representatives
    {x | D.scalarCurvature x ≤ rho⁻¹ ^ 2} hcompact
  refine ⟨s, fun x hx => hs hx, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨y, hy, hxy⟩
    obtain ⟨z, hzs, hyz⟩ := hcover y hy
    exact mem_iUnion₂.mpr ⟨z, hzs, hyz ▸ hxy⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
    exact ⟨y, hs hy, hxy⟩

end PoincareConjecture

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}

theorem exists_finite_core_components (Q : SingularLimitConclusion H) (rho : ℝ) :
    ∃ points : Finset (Q.extension.extended.slice T).carrier,
      (∀ x ∈ points, Q.terminal_scalar x ≤ rho⁻¹ ^ 2) ∧
      SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho =
        ⋃ x ∈ points, connectedComponent x := by
  have h := SurgeryTerminalCoreComponents.exists_finite_components
    (Q.extension.extended.connection T) rho (Q.isCompact_scalar_sublevel (rho⁻¹ ^ 2))
  simpa only [Q.terminal_scalar_eq] using h

end PoincareConjecture.SingularLimitConclusion
