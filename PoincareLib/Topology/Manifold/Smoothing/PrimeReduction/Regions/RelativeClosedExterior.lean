import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.Mathlib.RelativeRegionClosure

/-! # The relative frontier of a closed exterior

A closed set dense in its ambient interior is also regular closed in a
containing subspace. Its closed relative exterior meets it precisely along
the complete relative frontier.
-/

set_option autoImplicit false
open Set
namespace PoincareMT.M76

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

end PoincareMT.M76
