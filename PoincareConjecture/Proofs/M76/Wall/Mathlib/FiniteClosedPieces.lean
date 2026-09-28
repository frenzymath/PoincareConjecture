import Mathlib.Topology.Constructions









set_option autoImplicit false

open Set

namespace Set




theorem isOpen_preimage_iUnion_piece
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (S : ι → Set X) (hclosed : ∀ i, IsClosed (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j)) (i : ι) :
    IsOpen ((Subtype.val : (⋃ j, S j) → X) ⁻¹' S i) := by
  let A : Set X := ⋃ j : {j : ι // j ≠ i}, S j.val
  have hA : IsClosed A := isClosed_iUnion_of_finite fun j => hclosed j.val
  have heq : (Subtype.val : (⋃ j, S j) → X) ⁻¹' S i =
      ((Subtype.val : (⋃ j, S j) → X) ⁻¹' A)ᶜ := by
    ext x
    constructor
    · intro hx hxA
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxA
      exact disjoint_left.mp (hdisjoint (Ne.symm j.property)) hx hj
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp x.property
      by_cases hji : j = i
      · change (x : X) ∈ S i
        simpa only [hji] using hj
      · exact False.elim (hx (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩))
  rw [heq]
  exact (hA.preimage continuous_subtype_val).isOpen_compl

end Set
