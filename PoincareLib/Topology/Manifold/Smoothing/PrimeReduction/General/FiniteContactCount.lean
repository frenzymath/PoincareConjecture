import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.General.OriginalComplexEdgeGeometry

/-!
# Exact decrease after removing two contacts

The supported Kneser move removes two distinct selected contacts while
preserving every other contact.  This file records the finite-set part of
that argument; the geometric move must still construct the required set
equalities.
-/

set_option autoImplicit false

namespace PoincareMT.M76

/-- Erasing two distinct members of a finite contact set lowers its
cardinality by exactly two.  The hypotheses are the contact facts supplied
by a concrete supported move; no move or normalization is assumed here. -/
theorem card_erase_erase_of_mem_of_mem_of_ne
    {α : Type*} [DecidableEq α] (s : Finset α) {u v : α}
    (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) :
    ((s.erase u).erase v).card = s.card - 2 := by
  have hv' : v ∈ s.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu]
  omega

end PoincareMT.M76
