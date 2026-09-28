import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointPathLimit
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCapProjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointMidpointGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.QuarterPrismRescaling



set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_endpoint_lift_of_core_path
    {E ι : Type*} [TopologicalSpace E] [T2Space E] [Zero E] [Finite ι]
    {A B : ι → Set E} {S : Set E}
    (H : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (C : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hA : ∀ j, IsCompact (A j))
    (r : E → E) (hr : ContinuousOn r (⋃ j, prismTrim (H j)))
    (hrv : ∀ j x, r (C j x) = H j x)
    (R : ((⋃ j, prismTrim (H j)) \ ⋃ j, prismEnds (C j) : Set E) ≃ₜ
      ((⋃ j, B j) \ S : Set E)) (hR : ∀ x, (R x : E) = r x)
    {γ : ℝ → E} {ε : ℝ} (hε : 0 < ε)
    (hγ : ContinuousOn γ (Ioo 0 ε)) (hγ0 : ContinuousAt γ 0) (hzero : γ 0 ∈ S)
    (hinto : ∀ t ∈ Ioo 0 ε, γ t ∈ (⋃ j, B j) \ S) :
    ∃ (x : (⋃ j, prismEnds (C j))) (η : ℝ → (⋃ j, prismTrim (H j))),
      r x = γ 0 ∧ Tendsto η (𝓝[>] 0) (𝓝 (prismEndpointInclusion C x)) ∧
      ∀ t ∈ Ioo 0 ε, (η t : E) ∉ ⋃ j, prismEnds (C j) ∧ r (η t) = γ t := by
  let U := ⋃ j, prismTrim (H j)
  let Q := ⋃ j, prismEnds (C j)
  have hcompact (j) : IsCompact (prismTrim (H j)) := by
    let : CompactSpace (A j ×ˢ I : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp ((hA j).prod isCompact_Icc)
    let : CompactSpace (prismTrim (H j)) := (C j).compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  let : CompactSpace U := isCompact_iff_compactSpace.mp (isCompact_iUnion hcompact)
  let f : U → E := fun x => r x
  let D : Set U := {x | (x : E) ∉ Q}
  let flatten : D ≃ₜ (U \ Q : Set E) :=
    { toFun := fun x => ⟨x.1.1,x.1.2,x.2⟩
      invFun := fun x => ⟨⟨x.1,x.2.1⟩,x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let R' := flatten.trans R
  have hR' (x : D) : f x = (R' x : E) := (hR (flatten x)).symm
  have hfinite : (f ⁻¹' {γ 0}).Finite := by
    refine (finite_fiber_of_prism_cell_maps H C r hrv (γ 0)).1.of_injOn ?_
      Subtype.val_injective.injOn
    exact fun x hx => ⟨x.property,hx⟩
  obtain ⟨x,η,hx,hη,hηval⟩ := exists_endpoint_of_core_inverse_path
    hr.domRestrict R' hR' hε hγ hγ0 hinto hfinite
  change f x = γ 0 at hx
  have hxQ : (x : E) ∈ Q := by
    by_contra hxQ
    have hnot := (R' ⟨x,hxQ⟩).property.2
    rw [← hR'] at hnot
    change f x ∉ S at hnot
    rw [hx] at hnot
    exact hnot hzero
  refine ⟨⟨x,hxQ⟩,η,hx,hη,?_⟩
  intro t ht
  rw [hηval t ht]
  refine ⟨(R'.symm ⟨γ t,hinto t ht⟩).property,?_⟩
  change f (R'.symm ⟨γ t,hinto t ht⟩) = γ t
  rw [hR',R'.apply_symm_apply]

end PoincareConjecture.M76.PrismBelt
