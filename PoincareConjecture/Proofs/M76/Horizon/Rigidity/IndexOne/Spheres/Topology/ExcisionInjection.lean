import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.Injection

set_option autoImplicit false
open Set

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {P D : Set X}

theorem isClopen_sdiff_of_disjoint_frontier (hD : IsClosed D)
    (hfront : Disjoint P (frontier D)) :
    IsClopen ((Subtype.val : P → X) ⁻¹' (P \ D)) := by
  have heq : (Subtype.val : P → X) ⁻¹' D =
      (Subtype.val : P → X) ⁻¹' interior D := by
    ext x
    change (x : X) ∈ D ↔ (x : X) ∈ interior D
    constructor
    · intro hx
      apply (mem_interior_iff_notMem_frontier hx).mpr
      exact fun h => disjoint_left.mp hfront x.property h
    · exact fun hx => interior_subset hx
  have hclopen : IsClopen ((Subtype.val : P → X) ⁻¹' D) :=
    ⟨hD.preimage continuous_subtype_val, heq ▸ isOpen_interior.preimage continuous_subtype_val⟩
  have hcomp : (Subtype.val : P → X) ⁻¹' (P \ D) =
      ((Subtype.val : P → X) ⁻¹' D)ᶜ := by
    ext x
    exact and_iff_right x.property
  rw [hcomp]
  exact hclopen.compl

theorem ambient_injective_sdiff_of_disjoint_frontier
    (hD : IsClosed D) (hfront : Disjoint P (frontier D))
    (hinj : ∀ x : P, Function.Injective
      (map (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X)) x))
    (x : ↥(P \ D)) : Function.Injective
      (map (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(P \ D), X)) x) := by
  have hsub : P \ D ⊆ P := sdiff_subset
  have hi := inclusion_injective_of_isClopen hsub
    (isClopen_sdiff_of_disjoint_frontier hD hfront) x
  have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(P \ D), X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X)).comp
        (ContinuousMap.inclusion hsub) := rfl
  rw [heq, map_comp]
  exact (hinj (ContinuousMap.inclusion hsub x)).comp hi

end FundamentalGroup
