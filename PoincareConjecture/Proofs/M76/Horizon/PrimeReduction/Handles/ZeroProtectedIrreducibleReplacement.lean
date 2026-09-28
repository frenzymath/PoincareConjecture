import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.BoundaryRelativeIrreducibleAtlas
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.InteriorProtectedRetainedCore
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.ProtectedAtlasConjugation

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem hasHamiltonProtectedIrreducibleReplacement_of_card_eq_zero
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ))
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hzero : Fintype.card ι = 0) :
    HasHamiltonProtectedIrreducibleReplacement ι κ L e := by
  intro hdim hindex hdis hlattice he D hD
  let := hdis
  let := hlattice
  obtain ⟨bD⟩ := hD
  obtain ⟨charts,N,hN,hfront,hne,hI,hforward,hreverse⟩ :=
    exists_boundary_relative_irreducible_lattice_atlas L hdim hindex he bD
  obtain ⟨F,C,_,_,hFR,hF,_,hFD⟩ :=
    exists_zero_lattice_protected_ball_placement L hzero he bD hN (hne.mono inter_subset_left)
  obtain ⟨hopen,hprotected,hI',hforward',hreverse'⟩ :=
    protected_atlas_conjugation he hI hN hfront hforward hreverse F hFR hF
      hFD.image_subset
  exact ⟨range (fun c : charts => F.transOpenPartialHomeomorph c.val),
    F ⁻¹' N,hopen,hprotected,hI'.range,hforward'.range_target,hreverse'.range_source⟩

end PoincareConjecture.M76
