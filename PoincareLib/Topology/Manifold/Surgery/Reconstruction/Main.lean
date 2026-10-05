import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Statement
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Transport
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.Assembly

/-!
# M72 proof entry

The proof combines reverse-history induction, event reindexing,
immediate successors, and connectedness transport to the initial flow slice.
Transport.lean constructs the ledger from M52's local finiteness and the
component equivalence from the actual survivor and regular-slab maps.
M38 and M71 remain read-only services with explicit same-flow adapters.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-- Given an M52 global flow, finite extinction at an actual surgery time,
connected initial manifold, and the same flow's M38 local topology service,
construct its finite surgery ledger, a bijective enumeration of all event
non-survivor pieces, immediate-successor component transports, and a finite
connected-sum assembly of the nonempty connected initial slice from exactly
those pieces. Source: Morgan--Tian Proposition 15.3 and Corollary 15.4,
pp. 357--359; the neck-separation correction is retained by M38. -/
theorem m72FiniteReconstruction :
    M72FiniteReconstructionStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ N I
  exact ⟨m72ReconstructionConclusion I⟩

end PoincareMT
