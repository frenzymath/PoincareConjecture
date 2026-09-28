import Mathlib.Topology.Clopen

set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem isClopen_part_of_finite_closed_partition
    {X σ : Type*} [TopologicalSpace X] [Finite σ]
    (M : σ → Set X) (hclosed : ∀ i, IsClosed (M i))
    (hdisjoint : Pairwise fun i j => Disjoint (M i) (M j)) (i : σ) :
    IsClopen ((Subtype.val : (⋃ j, M j) → X) ⁻¹' M i) := by
  refine ⟨(hclosed i).preimage continuous_subtype_val, ?_⟩
  have hother : IsClosed (⋃ j : {j : σ // j ≠ i}, M j) :=
    isClosed_iUnion_of_finite (fun j => hclosed j)
  have heq : ((Subtype.val : (⋃ j, M j) → X) ⁻¹' M i) =
      ((Subtype.val : (⋃ j, M j) → X) ⁻¹' (⋃ j : {j : σ // j ≠ i}, M j))ᶜ := by
    ext x
    constructor
    · intro hx hother
      obtain ⟨j, hj⟩ := mem_iUnion.mp hother
      exact disjoint_left.mp (hdisjoint j.property) hj hx
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp x.property
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hx (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
  rw [heq]
  exact (hother.preimage continuous_subtype_val).isOpen_compl

end Poincare.Topology
