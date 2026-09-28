import Mathlib.Topology.Constructions










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X]



theorem closure_subtype_preimage_of_subset {R S : Set X} (hSR : S ⊆ R) :
    closure ((Subtype.val : R → X) ⁻¹' S) =
      (Subtype.val : R → X) ⁻¹' closure S := by
  have himage : (Subtype.val : R → X) '' ((Subtype.val : R → X) ⁻¹' S) = S := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, hSR hx⟩, hx, rfl⟩
  ext x
  rw [closure_subtype, himage]
  rfl




theorem regular_closed_subtype_preimage {R K : Set X}
    (hK : IsClosed K) (hKR : K ⊆ R) (hreg : closure (interior K) = K) :
    closure (interior ((Subtype.val : R → X) ⁻¹' K)) =
      (Subtype.val : R → X) ⁻¹' K := by
  have hsmall : (Subtype.val : R → X) ⁻¹' interior K ⊆
      interior ((Subtype.val : R → X) ⁻¹' K) :=
    preimage_interior_subset_interior_preimage continuous_subtype_val
  have hcl : closure ((Subtype.val : R → X) ⁻¹' interior K) =
      (Subtype.val : R → X) ⁻¹' K := by
    rw [closure_subtype_preimage_of_subset (interior_subset.trans hKR), hreg]
  apply Subset.antisymm
  · exact closure_minimal interior_subset (hK.preimage continuous_subtype_val)
  · exact hcl.symm.subset.trans (closure_mono hsmall)




theorem frontier_subtype_cut_of_closure {R U C : Set X}
    (hUR : U ⊆ R) (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' U))
    (hclosure : closure U = C) :
    frontier ((Subtype.val : R → X) ⁻¹' (R \ U)) =
      (Subtype.val : R → X) ⁻¹' (C \ U) := by
  have hcut : (Subtype.val : R → X) ⁻¹' (R \ U) =
      ((Subtype.val : R → X) ⁻¹' U)ᶜ := by
    ext x
    exact and_iff_right x.property
  rw [hcut, frontier_compl, frontier, hopen.interior_eq,
    closure_subtype_preimage_of_subset hUR, hclosure]
  rfl

end PoincareConjecture.M76
