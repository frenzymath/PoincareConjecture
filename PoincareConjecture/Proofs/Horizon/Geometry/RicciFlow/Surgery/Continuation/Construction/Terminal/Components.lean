import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Levels











noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.Terminal



theorem exists_finset_component_representatives {X : Type u} [TopologicalSpace X]
    [LocallyConnectedSpace X] (K : Set X) (hK : IsCompact K) :
    ∃ R : Finset X, (R : Set X) ⊆ K ∧
      ∀ x ∈ K, ∃ y ∈ R, connectedComponent x = connectedComponent y := by
  classical
  obtain ⟨R, hR⟩ := hK.elim_finite_subcover
    (fun y : K => connectedComponent y.val) (fun _ => isOpen_connectedComponent)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_connectedComponent⟩)
  refine ⟨R.image Subtype.val, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact z.property
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hR hx)
    exact ⟨y.val, Finset.mem_image.mpr ⟨y, hy, rfl⟩, (connectedComponent_eq hxy).symm⟩

end PoincareConjecture.Surgery.Terminal

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}



theorem exists_low_curvature_component_representatives
    (Q : SingularLimitConclusion H) (rho : ℝ) :
    ∃ R : Finset (Q.extension.extended.slice T).carrier,
      (∀ y ∈ R, Q.terminal_scalar y ≤ rho⁻¹ ^ 2) ∧
      (∀ x, Q.terminal_scalar x ≤ rho⁻¹ ^ 2 →
        ∃ y ∈ R, connectedComponent x = connectedComponent y) := by
  let : LocallyConnectedSpace (Q.extension.extended.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  have hK : IsCompact {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
    simpa only [Q.terminal_scalar_eq] using Q.isCompact_scalar_sublevel (rho⁻¹ ^ 2)
  obtain ⟨R, hR, hcover⟩ := Surgery.Terminal.exists_finset_component_representatives _ hK
  exact ⟨R, fun y hy => hR hy, hcover⟩


theorem finite_low_curvature_components (Q : SingularLimitConclusion H) (rho : ℝ) :
    {A : Set (Q.extension.extended.slice T).carrier |
      ∃ x, Q.terminal_scalar x ≤ rho⁻¹ ^ 2 ∧ A = connectedComponent x}.Finite := by
  obtain ⟨R, hR, hcover⟩ := Q.exists_low_curvature_component_representatives rho
  apply ((R.finite_toSet).image connectedComponent).subset
  rintro A ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hcover x hx
  exact ⟨y, hy, hxy.symm⟩

end PoincareConjecture.SingularLimitConclusion
