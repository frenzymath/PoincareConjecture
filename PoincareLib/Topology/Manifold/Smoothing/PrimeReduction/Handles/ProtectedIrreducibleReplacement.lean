import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Reattachment.HandleAddition.OriginalHandleIrreducibility
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Protection.OriginalIrreducibleExterior
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Handles.ZeroProtectedIrreducibleReplacement
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Handles.IndexTwoProtectedIrreducibleReplacement

/-! # Protected irreducible replacement for all lower lattice-handle indices

For index one the actual exterior replacement retains the marked ball and
whole-domain PL structure. Reattaching that ball yields the required
irreducible handle. The zero and two cases use their established constructions.
-/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)

theorem hasHamiltonProtectedIrreducibleReplacement_of_card_eq_one
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ))
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hi : Fintype.card ι = 1) :
    HasHamiltonProtectedIrreducibleReplacement ι κ L e := by
  intro hdim _hindex hdis hlattice he D hD
  let := hdis
  let := hlattice
  obtain ⟨b⟩ := hD
  obtain ⟨charts,N,hN,hprotected,hI,he',⟨b'⟩,hforward,hreverse,_⟩ :=
    b.exists_original_irreducible_exterior_atlas L he hdim hi
  exact ⟨charts,N,hN,hprotected,b'.isPLIrreducible_handle_of_exterior he' hdim hi hI,
    hforward,hreverse⟩

/-- Construct the unchanged universal protected replacement predicate from
the three actual lower-index geometric constructions. -/
theorem hasHamiltonProtectedIrreducibleReplacement
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ))
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3) :
    HasHamiltonProtectedIrreducibleReplacement ι κ L e := by
  intro hdim hindex hdis hlattice he D hD
  let := hdis
  let := hlattice
  have hcases : Fintype.card ι = 0 ∨ Fintype.card ι = 1 ∨ Fintype.card ι = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · exact hasHamiltonProtectedIrreducibleReplacement_of_card_eq_zero L e hzero hdim hindex
      hlattice he D hD
  · exact hasHamiltonProtectedIrreducibleReplacement_of_card_eq_one L e hone hdim hindex
      hlattice he D hD
  · exact hasHamiltonProtectedIrreducibleReplacement_of_card_eq_two L e htwo hdim hindex
      hlattice he D hD

end PoincareMT.M76
