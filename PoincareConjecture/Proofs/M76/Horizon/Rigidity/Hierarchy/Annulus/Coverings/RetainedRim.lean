import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.EssentialRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.ComponentGroups

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_boundary_rim_eq_of_supported_map
    (phi psi : C(H0, H0)) {R A : Set X0} (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    (theta : C0) :
    frontier R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta} =
      frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  apply and_congr_right
  intro hx
  rw [hamiltonZeroSecondCircleMap_ambient, hamiltonZeroSecondCircleMap_ambient,
    hfixed x (fun hxA => hx.2 (hAR hxA))]

theorem hamiltonZero_boundary_rim_covering_of_supported_map
    (phi psi : C(H0, H0)) {R A : Set X0} (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    (theta : C0)
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta)) :
    IsCoveringMap (hamiltonZeroSecondPhaseCircleMap psi (frontier R) theta) := by
  let H := Homeomorph.setCongr
    (hamiltonZero_boundary_rim_eq_of_supported_map phi psi hAR hfixed theta)
  convert hcover.comp_homeomorph H using 1
  funext x
  simp only [Function.comp_apply]
  rw [hamiltonZeroSecondPhaseCircleMap_ambient, hamiltonZeroSecondPhaseCircleMap_ambient]
  change (Q0 (hamiltonZeroAmbientMap psi x)).1.1 = (Q0 (hamiltonZeroAmbientMap phi x)).1.1
  rw [hfixed x (fun hxA => x.property.1.2 (hAR hxA))]

theorem nontrivial_hamiltonZero_retained_phase_component_at_rim
    (phi psi : C(H0, H0)) {R A : Set X0} (hR : IsClosed R) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    (theta : C0)
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    {S : Set X0} (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) x = S)
    (x : S) (hx : (x : X0) ∈ frontier R) : Nontrivial (FundamentalGroup S x) := by
  have hcoverPsi := hamiltonZero_boundary_rim_covering_of_supported_map
    phi psi hAR hfixed theta hcover
  let y : ↥(frontier R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) :=
    ⟨x, hx, (hS x.property).2⟩
  let : Nontrivial (FundamentalGroup (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta} : Set X0)
      ((ContinuousMap.inclusion hS) x)) :=
    (hamiltonZero_boundary_rim_injective_and_phase_nontrivial psi hR theta hcoverPsi y).2
  exact (FundamentalGroup.inclusion_surjective_of_whole_component hS hcomponent x).nontrivial

theorem exists_nontrivial_hamiltonZero_retained_phase_component
    (phi psi : C(H0, H0)) {R A : Set X0} (hR : IsClosed R) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    (theta : C0)
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    {S : Set X0} (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) x = S)
    (hmeets : (S ∩ frontier R).Nonempty) :
    ∃ x : S, (x : X0) ∈ frontier R ∧ Nontrivial (FundamentalGroup S x) := by
  obtain ⟨x, hxS, hxR⟩ := hmeets
  exact ⟨⟨x, hxS⟩, hxR, nontrivial_hamiltonZero_retained_phase_component_at_rim
    phi psi hR hAR hfixed theta hcover hS hcomponent ⟨x, hxS⟩ hxR⟩

theorem nontrivial_hamiltonZero_retained_rim_connectedComponent
    (phi psi : C(H0, H0)) {R A : Set X0} (hR : IsClosed R) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    (theta : C0)
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    (x : ↥(frontier R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})) :
    let S := connectedComponentIn (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) (x : X0)
    let hx : (x : X0) ∈ S := mem_connectedComponentIn
      ⟨hR.frontier_subset x.property.1, x.property.2⟩
    Nontrivial (FundamentalGroup S ⟨x, hx⟩) := by
  intro S hx
  exact nontrivial_hamiltonZero_retained_phase_component_at_rim
    phi psi hR hAR hfixed theta hcover (connectedComponentIn_subset _ _)
    (fun _ hy => (connectedComponentIn_eq hy).symm) ⟨x, hx⟩ x.property.1

end PoincareConjecture.M76
