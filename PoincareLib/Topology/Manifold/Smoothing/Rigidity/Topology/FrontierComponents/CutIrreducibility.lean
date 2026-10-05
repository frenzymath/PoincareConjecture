import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.FrontierComponents.Injection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.IncompressibleCutIrreducibility
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.SourcePhaseResidualModels

/-!
# Cut irreducibility from the constructed phase component models

The lower and upper models together cover the complete frontier. Their
actual whole components inject through the clopen phase partition and
the frontier. The existing cut theorem then retains original-atlas ball
fillings inside the selected cut domain.
-/

set_option autoImplicit false
open Set

namespace PoincareMT.M76

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
  {R Ω A B Nlower Nupper : Set X}

namespace FrontierResidualModel

omit [T2Space X] in
/-- The disjoint union of the two finite component index sets covers the
whole frontier of the actual cut domain. -/
theorem paired_components_cover (lower : FrontierResidualModel e Nlower A)
    (upper : FrontierResidualModel e Nupper B) (hfront : frontier R = A ∪ B) :
    (⋃ i : Fin lower.count ⊕ Fin upper.count,
      Sum.elim lower.components upper.components i) = frontier R := by
  simpa only [iUnion_sum, Sum.elim_inl, Sum.elim_inr, lower.cover, upper.cover] using hfront.symm

end FrontierResidualModel

/-- Actual component models with nontrivial groups and proved ambient
frontier injection imply irreducibility of the cut domain. -/
theorem IsPLIrreducible.of_frontier_component_models
    (hΩ : IsPLIrreducible e Ω) (hR : PLDomain e R) (hRΩ : R ⊆ Ω)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hfront : frontier R = A ∪ B)
    (lower : FrontierResidualModel e Nlower A)
    (upper : FrontierResidualModel e Nupper B)
    (hgroupsA : ∀ i (x : lower.components i),
      Nontrivial (FundamentalGroup (lower.components i) x))
    (hgroupsB : ∀ i (x : upper.components i),
      Nontrivial (FundamentalGroup (upper.components i) x))
    (hinj : ∀ x : frontier R, Function.Injective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier R, X)) x)) :
    IsPLIrreducible e R := by
  let M : Fin lower.count ⊕ Fin upper.count → Set X :=
    Sum.elim lower.components upper.components
  have hcover : (⋃ i, M i) = frontier R := lower.paired_components_cover upper hfront
  have hMfront (i) : M i ⊆ frontier R := by
    rw [← hcover]
    exact subset_iUnion M i
  have hMconn (i) : IsPreconnected (M i) := by
    cases i with
    | inl i => exact (lower.component i).2.1.isPreconnected
    | inr i => exact (upper.component i).2.1.isPreconnected
  have hgroups (i) (x : M i) : Nontrivial (FundamentalGroup (M i) x) := by
    cases i with
    | inl i => exact hgroupsA i x
    | inr i => exact hgroupsB i x
  have hambient (i) (x : M i) : Function.Injective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(M i, X)) x) := by
    cases i with
    | inl i =>
      exact FundamentalGroup.whole_phase_component_ambient_injective hA hB hAB hfront
        (lower.component i).2.2.1 (lower.component i).2.2.2 hinj x
    | inr i =>
      exact FundamentalGroup.whole_phase_component_ambient_injective hB hA hAB.symm
        (hfront.trans (union_comm A B))
        (upper.component i).2.2.1 (upper.component i).2.2.2 hinj x
  refine hΩ.of_incompressible_cut hR hRΩ M hMfront ?_ hMconn ?_
  · intro x hx _
    rw [← hcover] at hx
    exact mem_iUnion.mp hx
  · intro i x
    refine ⟨hgroups i x, ?_⟩
    let hMΩ := (hMfront i).trans (hR.closed.frontier_subset.trans hRΩ)
    let incl : C(M i, Ω) := ContinuousMap.inclusion hMΩ
    have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(M i, X)) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(Ω, X)).comp incl := rfl
    have hi := hambient i x
    rw [heq, FundamentalGroup.map_comp] at hi
    exact Function.Injective.of_comp hi

end PoincareMT.M76
