import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeRegionClosure








set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem frontier_relative_closed_exterior
    {X : Type*} [TopologicalSpace X] {R D : Set X}
    (hD : IsClosed D) (hDR : D ⊆ R) (hreg : closure (interior D) = D) :
    frontier ((Subtype.val : R → X) ⁻¹' closure (R \ D)) =
      (Subtype.val : R → X) ⁻¹' (closure (R \ D) ∩ D) := by
  let d : Set R := (Subtype.val : R → X) ⁻¹' D
  have hd : IsClosed d := hD.preimage continuous_subtype_val
  have hregular : closure (interior d) = d :=
    regular_closed_subtype_preimage hD hDR hreg
  have hE : (Subtype.val : R → X) ⁻¹' closure (R \ D) = closure dᶜ := by
    rw [← closure_subtype_preimage_of_subset (show R \ D ⊆ R from sdiff_subset)]
    congr 1
    ext x
    exact and_iff_right x.property
  rw [frontier_eq_closure_inter_closure,isClosed_closure.preimage continuous_subtype_val |>.closure_eq]
  have hc : ((Subtype.val : R → X) ⁻¹' closure (R \ D))ᶜ = interior d := by
    rw [hE,← interior_compl,compl_compl]
  rw [hc,hregular]
  rfl

end PoincareConjecture.M76
