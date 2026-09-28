import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointBoundaryLift
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismEndpointLifts

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_endpoint_collar_lift
    {E ι L : Type*} [TopologicalSpace E] [T2Space E] [Zero E] [Finite ι]
    [TopologicalSpace L] [LocallyPathConnectedSpace L]
    {A B : ι → Set E} {S : Set E}
    (H : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (C : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hA : ∀ j, IsCompact (A j))
    (r : E → E) (hr : ContinuousOn r (⋃ j, prismTrim (H j)))
    (hrv : ∀ j x, r (C j x) = H j x)
    (R : ((⋃ j, prismTrim (H j)) \ ⋃ j, prismEnds (C j) : Set E) ≃ₜ
      ((⋃ j, B j) \ S : Set E)) (hR : ∀ x, (R x : E) = r x)
    (φ : C(L × ℝ,E)) {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ a, φ (a,0) ∈ S)
    (hinto : ∀ a t, t ∈ Ioo 0 ε → φ (a,t) ∈ (⋃ j, B j) \ S) :
    ∃ (σ : C(L,(⋃ j, prismEnds (C j)))) (η : L × ℝ → (⋃ j, prismTrim (H j))),
      (∀ a, r (σ a) = φ (a,0)) ∧
      (∀ a, Tendsto η (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 (prismEndpointInclusion C (σ a)))) ∧
      ∀ a t, t ∈ Ioo 0 ε → (η (a,t) : E) ∉ ⋃ j, prismEnds (C j) ∧
        r (η (a,t)) = φ (a,t) := by
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
  have hfinite (a : L) : (f ⁻¹' {φ (a,0)}).Finite := by
    refine (finite_fiber_of_prism_cell_maps H C r hrv (φ (a,0))).1.of_injOn ?_
      Subtype.val_injective.injOn
    exact fun x hx => ⟨x.property,hx⟩
  obtain ⟨σ,η,hσ,hlim,hη,_⟩ := exists_continuous_core_inverse_boundary_lift
    hr.domRestrict R' hR' φ hε hinto hfinite
  change ∀ a, r (σ a) = φ (a,0) at hσ
  have hσQ (a : L) : (σ a : E) ∈ Q := by
    by_contra ha
    have hnot := (R' ⟨σ a,ha⟩).property.2
    rw [← hR'] at hnot
    change r (σ a) ∉ S at hnot
    rw [hσ a] at hnot
    exact hnot (hzero a)
  let σ' : C(L,Q) := ⟨fun a => ⟨σ a,hσQ a⟩,
    (continuous_subtype_val.comp σ.continuous).subtype_mk _⟩
  refine ⟨σ',η,hσ,hlim,?_⟩
  intro a t ht
  rw [hη a t ht]
  refine ⟨(R'.symm ⟨φ (a,t),hinto a t ht⟩).property,?_⟩
  change f (R'.symm ⟨φ (a,t),hinto a t ht⟩) = φ (a,t)
  rw [hR',R'.apply_symm_apply]

end PoincareConjecture.M76.PrismBelt
