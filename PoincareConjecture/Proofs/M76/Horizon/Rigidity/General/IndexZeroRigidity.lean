import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Applications.FailureComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.ProductFailureExclusion
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonTorusRigidity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.LatticeHandleRigidityTransport



set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V0" => (Fin 0 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))




theorem hasHamiltonRelativeTorusRigidity_fixed_zero
    {α β : Type*}
    (e : α → OpenPartialHomeomorph X0 V3)
    (d : β → OpenPartialHomeomorph X0 V3) :
    HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3) L0 e d := by
  intro hcard hlower hd hI hJ phi hphi hproper hidentity
  obtain ⟨F⟩ := hidentity
  rcases exists_hamiltonZero_rigidity_or_original_failure_component_products
      e d hI hd phi hphi F with
    hrigid | hfailure
  · exact hrigid
  obtain ⟨psi, hpsi, hphipsi, hidpsi, R, a, b, hab, hR, hIR, hcover, harc,
    hcomponents⟩ := hfailure
  have hnot : ¬ HamiltonZeroBoundaryFailureArc
      e R psi := by
    apply not_hamiltonZero_boundary_failure_of_component_products psi
      (hamiltonZeroRetainedTangentialMap psi (frontier R)) hcover (fun _ => rfl)
      a b hab
    intro x hx
    obtain ⟨hP, hconn, hIP, hPR, S₀, S₁, hS₀, hS₁, x₀, x₁,
      hS₀front, hS₁front, hdis, hcomponent₀, hcomponent₁,
      hnt₀, hnt₁, hinj₀, hinj₁, hphase₀, hphase₁, hcandidates,
      k, hcomm, H, hzero, hone, hfront, hrest⟩ := hcomponents x hx
    refine ⟨S₀, H.symm, ?_, ?_, ?_⟩
    · intro z
      have hzP : (z : X0) ∈ frontier R ↔ (z : X0) ∈ frontier
          (connectedComponentIn R x) := hPR z
      rw [hzP]
      have heq : (H (H.symm z) : X0) = z := congrArg Subtype.val (H.apply_symm_apply z)
      rw [← heq]
      simpa using hfront (H.symm z).1 (H.symm z).2
    · intro z hz
      have hw : H.symm z = ((H.symm z).1, (0 : unitInterval)) := by
        ext <;> simp [hz]
      have heq : H ((H.symm z).1, (0 : unitInterval)) = z := by
        rw [← hw]
        exact H.apply_symm_apply z
      have hzero' : (H ((H.symm z).1, (0 : unitInterval)) : X0) =
          ((H.symm z).1 : X0) := hzero (H.symm z).1
      rw [← congrArg Subtype.val heq, hzero']
      exact hphase₀ (H.symm z).1 (H.symm z).1.property
    · intro z hz
      have hw : H.symm z = ((H.symm z).1, (1 : unitInterval)) := by
        ext <;> simp [hz]
      have heq : H ((H.symm z).1, (1 : unitInterval)) = z := by
        rw [← hw]
        exact H.apply_symm_apply z
      have hzS₁ : (z : X0) ∈ S₁ := by
        rw [← hone]
        exact ⟨(H.symm z).1, congrArg Subtype.val heq⟩
      exact hphase₁ (z : X0) hzS₁
  exact False.elim (hnot harc)

theorem hasHamiltonRelativeTorusRigidity_zero
    (charts : Set (OpenPartialHomeomorph X0 V3))
    (d : (V0 × V3) → OpenPartialHomeomorph X0 V3) :
    HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3) L0
      (fun c : charts => (c : OpenPartialHomeomorph X0 V3)) d :=
  hasHamiltonRelativeTorusRigidity_fixed_zero _ d


theorem hasHamiltonRelativeTorusRigidity_of_card_zero_three
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    (Λ : Submodule ℤ (κ → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hι : Fintype.card ι = 0) (hκ : Fintype.card κ = 3)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) V3)
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) V3) :
    HasHamiltonRelativeTorusRigidity ι κ Λ e d := by
  intro _ _ hd hI hJ phi hphi hproper ⟨F⟩
  classical
  let τ : Fin 0 ≃ ι := (Fintype.equivFinOfCardEq hι).symm
  let σ : Fin 3 ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  obtain ⟨h, g, psi, hR, hg, hB, hconj, hd', hI', hJ', hpsi, hproper', hF'⟩ :=
    exists_lattice_handle_normalization τ σ L0 Λ e d hd hI hJ phi hphi hproper F
  obtain ⟨f, hf, ⟨Hf⟩, _⟩ := hasHamiltonRelativeTorusRigidity_fixed_zero _ _
    (by simp) (by simp) hd' hI' hJ' psi hpsi hproper' hF'
  exact exists_lattice_handle_rigidity_transport h g hR hg hB phi psi hconj F f hf Hf

end PoincareConjecture.M76
